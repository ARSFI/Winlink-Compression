Option Strict Off
Imports System.Collections.Generic
Imports System.Text
Imports System.Security.Cryptography

'
' This class implements the Compression, and CRC functions previously provided 
' in a no managed .DLL
'
' The Class names are:
'   Compression
'   Crc



Public Class Compression
    '
    ' lzh .net Class library v1.0
    ' Ported to C# by Peter Woods 08/22/2008 from the original
    ' Pascal version.
    ' Ported to VB by Peter Woods 10/20/2010 from the C# code
    '
    '--------------Original Header Below----------------- 
    ' 
    '  LZHUF.C English version 1.0
    '  Based on Japanese version 29-NOV-1988
    '  LZSS coded by Haruhiko OKUMURA
    '  Adaptive Huffman Coding coded by Haruyasu YOSHIZAKI
    '  Edited and translated to English by Kenji RIKITAKE
    '  Converted to Turbo Pascal 5.0
    '  by Peter Sawatzki with assistance of Wayne Sullivan
    '

    '
    ' Constants
    '
    '
    ' Synchonization object to support multi threading
    '
    Shared LZSync As New Object()

    '
    ' Define the string buffer size.  Note, was 4096 in the original pascal version.
    '
    Const N As Int32 = 2048

    '
    ' Define the size of the look-ahead buffer
    '
    Const F As Int32 = 60

    '
    ' Define the Threshold
    '
    Const Threshold As Int32 = 2

    '
    ' Set the NULL value to the size of the string buffer
    '
    Const NodeNIL As Int32 = N

    '
    ' Huffman coding parameters
    '
    Const NChar As Int32 = (256 - Threshold) + F

    '
    ' Define the table size
    ' character code = 0..N_CHAR-1
    '
    Const T As Int32 = (NChar * 2) - 1

    '
    ' Define the Root position
    '
    Const R As Int32 = T - 1

    '
    ' MAx frequency is 32678
    '
    Const MaxFreq As Int32 = &H8000

    '
    ' CRC polynomial
    '
    Const CRCPoly As Int32 = &H18408

    '
    ' Allocate fixed size buffers
    '
    '
    ' textBuf [0..N+F-2] Byte->Byte
    ' 
    Const TBSize As Int32 = N + F - 2
    Shared textBufMask As Int32 = &HFF
    Shared textBuf As Byte() = New Byte(TBSize + 1) {}

    '
    ' lSon [0..N] Word->UInt16
    '
    Shared lSon As Int32() = New Int32(N + 1) {}

    '
    ' dad [0..N] Word->UInt16
    '
    Shared dad As Int32() = New Int32(N + 1) {}

    '
    ' rSon [0..N+256] Word->UInt16
    '
    Shared rSon As Int32() = New Int32(N + 256 + 1) {}

    '
    ' Cumulative freq table [0..T] Word->UInt16
    '
    Shared freq As Int32() = New Int32(T + 1) {}

    '
    ' Pointing children nodes (son[], son[] + 1) [0..T-1] Word->UInt16
    '
    Shared son As Int32() = New Int32(T) {}

    '
    ' Pointing parent nodes use [0..T-1]. Area [T..(T + N_CHAR - 1)] are pointers for leaves
    ' Word->UInt16
    '
    Shared parent As Int32() = New Int32(T + NChar) {}

    '
    ' Tables for encoding/decoding upper 6 bits of sliding dictionary pointer
    ' encoder table}
    '
    ' Position Encode length
    '
    Shared p_len As Byte() = {&H3, &H4, &H4, &H4, &H5, &H5, _
     &H5, &H5, &H5, &H5, &H5, &H5, _
     &H6, &H6, &H6, &H6, &H6, &H6, _
     &H6, &H6, &H6, &H6, &H6, &H6, _
     &H7, &H7, &H7, &H7, &H7, &H7, _
     &H7, &H7, &H7, &H7, &H7, &H7, _
     &H7, &H7, &H7, &H7, &H7, &H7, _
     &H7, &H7, &H7, &H7, &H7, &H7, _
     &H8, &H8, &H8, &H8, &H8, &H8, _
     &H8, &H8, &H8, &H8, &H8, &H8, _
     &H8, &H8, &H8, &H8}

    '
    ' Position Encode Table
    '
    Shared p_code As Int32() = {&H0, &H20, &H30, &H40, &H50, &H58, _
     &H60, &H68, &H70, &H78, &H80, &H88, _
     &H90, &H94, &H98, &H9C, &HA0, &HA4, _
     &HA8, &HAC, &HB0, &HB4, &HB8, &HBC, _
     &HC0, &HC2, &HC4, &HC6, &HC8, &HCA, _
     &HCC, &HCE, &HD0, &HD2, &HD4, &HD6, _
     &HD8, &HDA, &HDC, &HDE, &HE0, &HE2, _
     &HE4, &HE6, &HE8, &HEA, &HEC, &HEE, _
     &HF0, &HF1, &HF2, &HF3, &HF4, &HF5, _
     &HF6, &HF7, &HF8, &HF9, &HFA, &HFB, _
     &HFC, &HFD, &HFE, &HFF}

    '
    ' Position decode table
    '
    Shared d_code As Int32() = {&H0, &H0, &H0, &H0, &H0, &H0, _
     &H0, &H0, &H0, &H0, &H0, &H0, _
     &H0, &H0, &H0, &H0, &H0, &H0, _
     &H0, &H0, &H0, &H0, &H0, &H0, _
     &H0, &H0, &H0, &H0, &H0, &H0, _
     &H0, &H0, &H1, &H1, &H1, &H1, _
     &H1, &H1, &H1, &H1, &H1, &H1, _
     &H1, &H1, &H1, &H1, &H1, &H1, _
     &H2, &H2, &H2, &H2, &H2, &H2, _
     &H2, &H2, &H2, &H2, &H2, &H2, _
     &H2, &H2, &H2, &H2, &H3, &H3, _
     &H3, &H3, &H3, &H3, &H3, &H3, _
     &H3, &H3, &H3, &H3, &H3, &H3, _
     &H3, &H3, &H4, &H4, &H4, &H4, _
     &H4, &H4, &H4, &H4, &H5, &H5, _
     &H5, &H5, &H5, &H5, &H5, &H5, _
     &H6, &H6, &H6, &H6, &H6, &H6, _
     &H6, &H6, &H7, &H7, &H7, &H7, _
     &H7, &H7, &H7, &H7, &H8, &H8, _
     &H8, &H8, &H8, &H8, &H8, &H8, _
     &H9, &H9, &H9, &H9, &H9, &H9, _
     &H9, &H9, &HA, &HA, &HA, &HA, _
     &HA, &HA, &HA, &HA, &HB, &HB, _
     &HB, &HB, &HB, &HB, &HB, &HB, _
     &HC, &HC, &HC, &HC, &HD, &HD, _
     &HD, &HD, &HE, &HE, &HE, &HE, _
     &HF, &HF, &HF, &HF, &H10, &H10, _
     &H10, &H10, &H11, &H11, &H11, &H11, _
     &H12, &H12, &H12, &H12, &H13, &H13, _
     &H13, &H13, &H14, &H14, &H14, &H14, _
     &H15, &H15, &H15, &H15, &H16, &H16, _
     &H16, &H16, &H17, &H17, &H17, &H17, _
     &H18, &H18, &H19, &H19, &H1A, &H1A, _
     &H1B, &H1B, &H1C, &H1C, &H1D, &H1D, _
     &H1E, &H1E, &H1F, &H1F, &H20, &H20, _
     &H21, &H21, &H22, &H22, &H23, &H23, _
     &H24, &H24, &H25, &H25, &H26, &H26, _
     &H27, &H27, &H28, &H28, &H29, &H29, _
     &H2A, &H2A, &H2B, &H2B, &H2C, &H2C, _
     &H2D, &H2D, &H2E, &H2E, &H2F, &H2F, _
     &H30, &H31, &H32, &H33, &H34, &H35, _
     &H36, &H37, &H38, &H39, &H3A, &H3B, _
     &H3C, &H3D, &H3E, &H3F}

    '
    ' Position decode length
    '
    Shared d_len As Int32() = {&H3, &H3, &H3, &H3, &H3, &H3, _
     &H3, &H3, &H3, &H3, &H3, &H3, _
     &H3, &H3, &H3, &H3, &H3, &H3, _
     &H3, &H3, &H3, &H3, &H3, &H3, _
     &H3, &H3, &H3, &H3, &H3, &H3, _
     &H3, &H3, &H4, &H4, &H4, &H4, _
     &H4, &H4, &H4, &H4, &H4, &H4, _
     &H4, &H4, &H4, &H4, &H4, &H4, _
     &H4, &H4, &H4, &H4, &H4, &H4, _
     &H4, &H4, &H4, &H4, &H4, &H4, _
     &H4, &H4, &H4, &H4, &H4, &H4, _
     &H4, &H4, &H4, &H4, &H4, &H4, _
     &H4, &H4, &H4, &H4, &H4, &H4, _
     &H4, &H4, &H5, &H5, &H5, &H5, _
     &H5, &H5, &H5, &H5, &H5, &H5, _
     &H5, &H5, &H5, &H5, &H5, &H5, _
     &H5, &H5, &H5, &H5, &H5, &H5, _
     &H5, &H5, &H5, &H5, &H5, &H5, _
     &H5, &H5, &H5, &H5, &H5, &H5, _
     &H5, &H5, &H5, &H5, &H5, &H5, _
     &H5, &H5, &H5, &H5, &H5, &H5, _
     &H5, &H5, &H5, &H5, &H5, &H5, _
     &H5, &H5, &H5, &H5, &H5, &H5, _
     &H5, &H5, &H5, &H5, &H5, &H5, _
     &H6, &H6, &H6, &H6, &H6, &H6, _
     &H6, &H6, &H6, &H6, &H6, &H6, _
     &H6, &H6, &H6, &H6, &H6, &H6, _
     &H6, &H6, &H6, &H6, &H6, &H6, _
     &H6, &H6, &H6, &H6, &H6, &H6, _
     &H6, &H6, &H6, &H6, &H6, &H6, _
     &H6, &H6, &H6, &H6, &H6, &H6, _
     &H6, &H6, &H6, &H6, &H6, &H6, _
     &H7, &H7, &H7, &H7, &H7, &H7, _
     &H7, &H7, &H7, &H7, &H7, &H7, _
     &H7, &H7, &H7, &H7, &H7, &H7, _
     &H7, &H7, &H7, &H7, &H7, &H7, _
     &H7, &H7, &H7, &H7, &H7, &H7, _
     &H7, &H7, &H7, &H7, &H7, &H7, _
     &H7, &H7, &H7, &H7, &H7, &H7, _
     &H7, &H7, &H7, &H7, &H7, &H7, _
     &H8, &H8, &H8, &H8, &H8, &H8, _
     &H8, &H8, &H8, &H8, &H8, &H8, _
     &H8, &H8, &H8, &H8}

    '
    ' CRC Table 
    ' Word->UInt16
    '
    Shared CRCMask As Int32 = &HFFFF
    Shared CRCTable As Int32() = {&H0, &H1021, &H2042, &H3063, &H4084, &H50A5, _
     &H60C6, &H70E7, &H8108, &H9129, &HA14A, &HB16B, _
     &HC18C, &HD1AD, &HE1CE, &HF1EF, &H1231, &H210, _
     &H3273, &H2252, &H52B5, &H4294, &H72F7, &H62D6, _
     &H9339, &H8318, &HB37B, &HA35A, &HD3BD, &HC39C, _
     &HF3FF, &HE3DE, &H2462, &H3443, &H420, &H1401, _
     &H64E6, &H74C7, &H44A4, &H5485, &HA56A, &HB54B, _
     &H8528, &H9509, &HE5EE, &HF5CF, &HC5AC, &HD58D, _
     &H3653, &H2672, &H1611, &H630, &H76D7, &H66F6, _
     &H5695, &H46B4, &HB75B, &HA77A, &H9719, &H8738, _
     &HF7DF, &HE7FE, &HD79D, &HC7BC, &H48C4, &H58E5, _
     &H6886, &H78A7, &H840, &H1861, &H2802, &H3823, _
     &HC9CC, &HD9ED, &HE98E, &HF9AF, &H8948, &H9969, _
     &HA90A, &HB92B, &H5AF5, &H4AD4, &H7AB7, &H6A96, _
     &H1A71, &HA50, &H3A33, &H2A12, &HDBFD, &HCBDC, _
     &HFBBF, &HEB9E, &H9B79, &H8B58, &HBB3B, &HAB1A, _
     &H6CA6, &H7C87, &H4CE4, &H5CC5, &H2C22, &H3C03, _
     &HC60, &H1C41, &HEDAE, &HFD8F, &HCDEC, &HDDCD, _
     &HAD2A, &HBD0B, &H8D68, &H9D49, &H7E97, &H6EB6, _
     &H5ED5, &H4EF4, &H3E13, &H2E32, &H1E51, &HE70, _
     &HFF9F, &HEFBE, &HDFDD, &HCFFC, &HBF1B, &HAF3A, _
     &H9F59, &H8F78, &H9188, &H81A9, &HB1CA, &HA1EB, _
     &HD10C, &HC12D, &HF14E, &HE16F, &H1080, &HA1, _
     &H30C2, &H20E3, &H5004, &H4025, &H7046, &H6067, _
     &H83B9, &H9398, &HA3FB, &HB3DA, &HC33D, &HD31C, _
     &HE37F, &HF35E, &H2B1, &H1290, &H22F3, &H32D2, _
     &H4235, &H5214, &H6277, &H7256, &HB5EA, &HA5CB, _
     &H95A8, &H8589, &HF56E, &HE54F, &HD52C, &HC50D, _
     &H34E2, &H24C3, &H14A0, &H481, &H7466, &H6447, _
     &H5424, &H4405, &HA7DB, &HB7FA, &H8799, &H97B8, _
     &HE75F, &HF77E, &HC71D, &HD73C, &H26D3, &H36F2, _
     &H691, &H16B0, &H6657, &H7676, &H4615, &H5634, _
     &HD94C, &HC96D, &HF90E, &HE92F, &H99C8, &H89E9, _
     &HB98A, &HA9AB, &H5844, &H4865, &H7806, &H6827, _
     &H18C0, &H8E1, &H3882, &H28A3, &HCB7D, &HDB5C, _
     &HEB3F, &HFB1E, &H8BF9, &H9BD8, &HABBB, &HBB9A, _
     &H4A75, &H5A54, &H6A37, &H7A16, &HAF1, &H1AD0, _
     &H2AB3, &H3A92, &HFD2E, &HED0F, &HDD6C, &HCD4D, _
     &HBDAA, &HAD8B, &H9DE8, &H8DC9, &H7C26, &H6C07, _
     &H5C64, &H4C45, &H3CA2, &H2C83, &H1CE0, &HCC1, _
     &HEF1F, &HFF3E, &HCF5D, &HDF7C, &HAF9B, &HBFBA, _
     &H8FD9, &H9FF8, &H6E17, &H7E36, &H4E55, &H5E74, _
     &H2E93, &H3EB2, &HED1, &H1EF0}

    '
    ' Processing buffers
    '

    Shared inBuf As Byte() = Nothing
    Shared outBuf As Byte() = Nothing

    Shared inPtr As Int32 = 0
    Shared inEnd As Int32 = 0
    Shared outPtr As Int32 = 0

    Shared CRC As Int32
    Shared EncDec As Boolean = False ' true for Encode, false for Decode
    Shared getBuf As Int32 = 0
    Shared getLen As Int32 = 0
    Shared putBuf As Int32 = 0
    Shared putLen As Int32 = 0

    Shared textSize As Int32 = 0
    Shared codeSize As Int32 = 0

    Shared matchPosition As Int32 = 0
    Shared matchLength As Int32 = 0

    '
    ' Main entry points
    '
    Public Shared Function Encode(ByVal iBuf As Byte(), ByRef oBuf As Byte(), ByVal prependCRC As Boolean) As Int32
      Dim tmp As Int32
        Encode = Encode(iBuf, oBuf, tmp, prependCRC)
    End Function

   Public Shared Function Encode(ByVal iBuf As Byte(), ByRef oBuf As Byte(), ByVal retCRC As Int32) As Int32
      Encode = Encode(iBuf, oBuf, retCRC, False)
   End Function

   Public Shared Function Encode(ByVal iBuf As Byte(), ByRef oBuf As Byte(), ByVal retCRC As Int32, ByVal prependCRC As Boolean) As Int32
      '
      ' Encoding/Compressing
      '
      Dim i As Int32
      Dim c As Int32
      Dim len As Int32
      Dim r As Int32
      Dim s As Int32
      Dim last_match_length As Int32
      Dim j As Int32 = 0

        SyncLock LZSync
            '
            ' The lock makes the code thread-safe
            '
            ' Allocate work buffers to hold the incoming message.
            inBuf = New Byte(iBuf.Length + 100) {}
            outBuf = New Byte(iBuf.Length * 2 + 10000) {}

            Init()
            EncDec = True

            For i = 0 To iBuf.Length - 1
                inBuf(inEnd) = iBuf(i)
                inEnd += 1
            Next

            putc(CType(inEnd And &HFF, Byte))
            putc(CType((inEnd >> 8) And &HFF, Byte))
            putc(CType((inEnd >> 16) And &HFF, Byte))
            putc(CType((inEnd >> 24) And &HFF, Byte))

            codeSize += 4

            If inEnd = 0 Then
                oBuf = New Byte(-1) {}
                retCRC = 0
                ' Free the work buffers
                inBuf = Nothing
                outBuf = Nothing
                Return codeSize
            End If
            textSize = 0
            StartHuff()
            InitTree()
            s = 0
            r = N - F
            For i = 0 To r - 1
                'fillchar(text_buf[0],r,' ');
                textBuf(i) = CType(&H20, Byte)
            Next

            len = 0
            While (len < F) AndAlso (inPtr < inEnd)
                textBuf(r + len) = CType(getc(), Byte) And &HFF
                len += 1
            End While
            textSize = len
            For i = 1 To F
                InsertNode(r - i)
            Next
            InsertNode(r)
            Do
                If matchLength > len Then
                    matchLength = len
                End If
                If matchLength <= Threshold Then
                    matchLength = 1
                    EncodeChar(textBuf(r))
                Else
                    EncodeChar((255 - Threshold) + matchLength)
                    EncodePosition(matchPosition)
                End If
                last_match_length = matchLength
                i = 0
                While (i < last_match_length) AndAlso (inPtr < inEnd)
                    i += 1
                    DeleteNode(s)
                    c = getc()
                    textBuf(s) = CType(c, Byte) And &HFF
                    If s < F - 1 Then
                        textBuf(s + N) = CType(c, Byte)
                    End If
                    s = (s + 1) And (N - 1)
                    r = (r + 1) And (N - 1)
                    InsertNode(r)
                End While
                textSize += i
                While i < last_match_length
                    i += 1
                    DeleteNode(s)
                    s = (s + 1) And (N - 1)
                    r = (r + 1) And (N - 1)
                    len -= 1
                    If len > 0 Then
                        InsertNode(r)
                    End If
                End While
            Loop While len > 0
            EncodeEnd()
            retCRC = GetCRC()

            '
            ' Create a buffer to hold the results
            '
            If prependCRC Then
                oBuf = New Byte(codeSize + 1) {}
                oBuf(0) = CType((retCRC >> 8) And &HFF, Byte)
                oBuf(1) = CType(retCRC And &HFF, Byte)
                j = 2
            Else
                oBuf = New Byte(codeSize - 1) {}
                j = 0
            End If

            For i = 0 To codeSize - 1
                oBuf(j) = outBuf(i)
                j += 1
            Next

            If prependCRC Then
                codeSize += 2
            End If

            Encode = codeSize
            ' Free the work buffers
            inBuf = Nothing
            outBuf = Nothing
        End SyncLock
    End Function

    Public Shared Function Decode(ByVal iBuf As Byte(), ByRef oBuf As Byte(), ByVal checkCRC As Boolean, ByVal intExpectedUncompressedSize As Integer) As Int32
        Dim tmp As UInt16 = 0
        Return DecodeWork(iBuf, oBuf, tmp, checkCRC, intExpectedUncompressedSize)
    End Function

    Public Shared Function Decode(ByVal iBuf As Byte(), ByRef oBuf As Byte(), ByVal retCRC As UInt16, ByVal intExpectedUncompressedSize As Integer) As Int32
        Return DecodeWork(iBuf, oBuf, retCRC, False, intExpectedUncompressedSize)
    End Function

    Public Shared Function DecodeWork(ByVal iBuf As Byte(), ByRef oBuf As Byte(), ByVal retCRC As UInt16, ByVal checkCRC As Boolean, ByVal intExpectedUncompressedSize As Integer) As Int32
        '
        ' Decoding/Uncompressing
        '
        Dim i As Int32
        Dim j As Int32
        Dim k As Int32
        Dim r As Int32
        Dim c As Int32
        Dim count As Int32
        Dim iBufStart As Int32 = 0
        Dim suppliedCRC As Int32 = 0

        SyncLock LZSync
            '
            ' The lock makes the code thread-safe
            '
            ' Allocate work buffers to hold the incoming message.
            inBuf = New Byte(iBuf.Length + 100) {}
            outBuf = New Byte(intExpectedUncompressedSize + 10000) {}

            EncDec = False
            Init()

            If checkCRC Then
                iBufStart = 2
                suppliedCRC = CType(iBuf(1), Int32) And &HFF
                suppliedCRC = suppliedCRC Or (CType(iBuf(0), Int32) << 8)
            End If

            For i = iBufStart To iBuf.Length - 1
                '
                ' Load the user supplied buffer into the internal processing buffer
                '
                inBuf(inEnd) = iBuf(i)
                inEnd += 1
            Next

            '
            ' Read size of original text
            '
            textSize = getc()
            textSize = textSize Or (getc() << 8)
            textSize = textSize Or (getc() << 16)
            textSize = textSize Or (getc() << 24)

            If textSize = 0 Then
                oBuf = New Byte(-1) {}
                retCRC = 0
                DecodeWork = textSize
                ' Free the work buffers
                inBuf = Nothing
                outBuf = Nothing
                Return textSize
            End If

            StartHuff()

            For i = 0 To (N - F) - 1
                'fillchar(text_buf[0],N-F,' ');
                textBuf(i) = CType(&H20, Byte)
            Next

            r = N - F
            count = 0
            While count < textSize
                c = DecodeChar()
                If c < 256 Then
                    putc(CType(c And &HFF, Byte))
                    textBuf(r) = CType(c And &HFF, Byte)
                    r = (r + 1) And (N - 1)
                    count += 1
                Else
                    i = ((r - DecodePosition()) - 1) And (N - 1)
                    j = (c - 255) + Threshold
                    For k = 0 To j - 1
                        c = CType(textBuf((i + k) And (N - 1)), Int32)
                        putc(CType(c And &HFF, Byte))
                        textBuf(r) = CType(c And &HFF, Byte)
                        r = (r + 1) And (N - 1)
                        count += 1
                    Next
                End If
            End While

            oBuf = New Byte(count - 1) {}
            retCRC = GetCRC()

            For i = 0 To count - 1
                oBuf(i) = outBuf(i)
            Next

            If checkCRC AndAlso (retCRC <> suppliedCRC) Then
                '
                ' Check the CRC.  Return 0 if mismatch
                '
                count = 0
            End If
            ' Free the work buffers
            inBuf = Nothing
            outBuf = Nothing
            Return count
        End SyncLock

    End Function

   Public Shared Function GetCRC() As Int32
      Return CType(Swap(CRC And &HFFFF), Int32)
   End Function

    Private Shared Sub Init()
        '
        ' Initialize all structures pointers and counters
        '
        inPtr = 0
        inEnd = 0
        outPtr = 0
        'outEnd = 0;

        getBuf = 0
        getLen = 0
        putBuf = 0
        putLen = 0

        textSize = 0
        codeSize = 0

        matchPosition = 0
        matchLength = 0

        InitArrayB(inBuf)
        InitArrayB(outBuf)

        InitArrayB(textBuf)

        InitArrayI(lSon)
        InitArrayI(dad)
        InitArrayI(rSon)
        InitArrayI(freq)

        InitArrayI(parent)
        InitArrayI(son)

        CRC = 0
    End Sub

    Private Shared Sub DoCRC(ByVal c As Int32)
        '
        ' Update running tally of CRC
        '
        CRC = ((CRC << 8) Xor CRCTable((CRC >> 8) Xor c)) And CRCMask
    End Sub

    Private Shared Function getc() As Integer
        '
        ' Get a character from the input buffer
        '
        Dim c As Int32 = 0
        If inPtr < inEnd Then
            c = CType(inBuf(inPtr), Int32) And &HFF
            inPtr += 1
            If Not EncDec Then
                '
                ' Do CRC on input for Decode
                '
                DoCRC(c)
            End If
        End If
        Return c
    End Function

    Private Shared Sub putc(ByVal c As Int32)
        '
        ' Write a character from the output buffer
        '
        outBuf(outPtr) = CType(c And &HFF, Byte)
        outPtr += 1
        If EncDec Then
            '
            ' Do CRC on output for Encode
            '
            DoCRC(c)
        End If
    End Sub

    Private Shared Sub InitTree()
        '
        ' Initializing tree
        '
        Dim i As Int32
        For i = N + 1 To N + 256
            ' {root
            rSon(i) = NodeNIL
        Next

        For i = 0 To N - 1
            '{node}
            dad(i) = NodeNIL
        Next
    End Sub

    Private Shared Sub InsertNode(ByVal r As Int32)
        '
        ' Insert nodes to the tree
        '

        Dim i As Int32
        Dim p As Int32
        Dim geq As Boolean
        Dim c As Int32

        geq = True
        p = N + 1 + textBuf(r)
        rSon(r) = NodeNIL
        lSon(r) = NodeNIL
        matchLength = 0
        While True
            If geq Then
                If rSon(p) = NodeNIL Then
                    rSon(p) = r
                    dad(r) = p
                    Return
                Else
                    p = rSon(p)
                End If
            Else
                If lSon(p) = NodeNIL Then
                    lSon(p) = r
                    dad(r) = p
                    Return
                Else
                    p = lSon(p)
                End If
            End If
            i = 1
            While (i < F) AndAlso (textBuf(r + i) = textBuf(p + i))
                i += 1
            End While

            geq = (textBuf(r + i) >= textBuf(p + i)) OrElse (i = F)

            If i > Threshold Then
                If i > matchLength Then
                    matchPosition = ((r - p) And (N - 1)) - 1
                    matchLength = i
                    If matchLength >= F Then
                        Exit While
                    End If
                End If
                If i = matchLength Then
                    c = ((r - p) And (N - 1)) - 1
                    If c < matchPosition Then
                        matchPosition = c
                    End If
                End If
            End If
        End While

        dad(r) = dad(p)
        lSon(r) = lSon(p)
        rSon(r) = rSon(p)
        dad(lSon(p)) = r
        dad(rSon(p)) = r
        If rSon(dad(p)) = p Then
            rSon(dad(p)) = r
        Else
            lSon(dad(p)) = r
        End If
        dad(p) = NodeNIL
        ' remove p
    End Sub

    Private Shared Sub DeleteNode(ByVal p As Int32)
        '
        ' Delete node from the tree
        '
        Dim q As Int32

        If dad(p) = NodeNIL Then
            ' unregistered
            Return
        End If

        If rSon(p) = NodeNIL Then
            q = lSon(p)
        Else
            If lSon(p) = NodeNIL Then
                q = rSon(p)
            Else
                q = lSon(p)

                If rSon(q) <> NodeNIL Then
                    Do
                        q = rSon(q)
                    Loop While rSon(q) <> NodeNIL
                    rSon(dad(q)) = lSon(q)
                    dad(lSon(q)) = dad(q)
                    lSon(q) = lSon(p)
                    dad(lSon(p)) = q
                End If
                rSon(q) = rSon(p)
                dad(rSon(p)) = q
            End If
        End If
        dad(q) = dad(p)
        If rSon(dad(p)) = p Then
            rSon(dad(p)) = q
        Else
            lSon(dad(p)) = q
        End If
        dad(p) = NodeNIL
    End Sub

    Private Shared Function GetBit() As Int32
        '
        ' Get one bit
        '
        Dim retVal As Int32
        While getLen <= 8
            getBuf = (getBuf Or (getc() << (8 - getLen))) And &HFFFF
            getLen += 8
        End While
        retVal = (getBuf >> 15) And &H1
        getBuf = (getBuf << 1) And &HFFFF
        getLen -= 1
        Return retVal
    End Function

    Private Shared Function GetByte() As Int32
        '
        ' Get one byte
        '
        Dim retVal As Int32
        While getLen <= 8
            getBuf = (getBuf Or (getc() << (8 - getLen))) And &HFFFF
            getLen += 8
        End While
        retVal = Hi(getBuf) And &HFF
        getBuf = (getBuf << 8) And &HFFFF
        getLen -= 8
        Return retVal
    End Function

    Private Shared Sub Putcode(ByVal n As Int32, ByVal c As Int32)
        '
        ' Output 'n' bits
        '
        putBuf = (putBuf Or (c >> putLen)) And &HFFFF
        putLen += n
        If putLen >= 8 Then
            putc(Hi(putBuf) And &HFF)
            putLen -= 8
            If putLen >= 8 Then
                putc(Lo(putBuf) And &HFF)
                codeSize += 2
                putLen -= 8
                putBuf = (c << (n - putLen)) And &HFFFF
            Else
                putBuf = Swap(putBuf And &HFF)
                codeSize += 1
            End If
        End If
    End Sub

    Private Shared Sub StartHuff()
        '
        ' Initialize freq tree
        '
        Dim i As Int32
        Dim j As Int32

        For i = 0 To NChar - 1
            freq(i) = 1
            son(i) = i + T
            parent(i + T) = i
        Next
        i = 0
        j = NChar
        While j <= R
            freq(j) = (freq(i) + freq(i + 1)) And &HFFFF
            son(j) = i
            parent(i) = j
            parent(i + 1) = j
            i += 2
            j += 1
        End While
        freq(T) = &HFFFF
        parent(R) = 0
    End Sub

    Private Shared Sub reconst()
        '
        ' Reconstruct freq tree
        '
        Dim i As Int32
        Dim j As Int32
        Dim k As Int32
        Dim f As Int32
        Dim n As Int32

        '
        ' Halven cumulative freq for leaf nodes
        '
        j = 0
        For i = 0 To T - 1
            If son(i) >= T Then
                freq(j) = (freq(i) + 1) >> 1
                son(j) = son(i)
                j += 1
            End If
        Next

        '
        ' Make a tree : first, connect children nodes
        '
        i = 0
        j = NChar
        While j < T
            k = i + 1
            f = (freq(i) + freq(k)) And &HFFFF
            freq(j) = f
            k = j - 1
            While f < freq(k)
                k -= 1
            End While
            k += 1

            '
            ' Original code segment
            ' l:= (j-k)*2;
            ' move(freq[k],freq[k+1],l);
            ' freq[k]:= f;
            ' move(son[k],son[k+1],l);
            ' son[k]:= i;
            '
            ' New code segment.
            '
            For n = j To k + 1 Step -1
                freq(n) = freq(n - 1)
                son(n) = son(n - 1)
            Next
            freq(k) = f
            son(k) = i

            i += 2
            j += 1
        End While

        '
        ' Connect parent nodes
        '
        For i = 0 To T - 1
            k = son(i)
            parent(k) = i
            If k < T Then
                parent(k + 1) = i
            End If
        Next
    End Sub

    Private Shared Sub update(ByVal c As Int32)
        '
        ' Update freq tree
        '
        Dim i As Int32
        Dim j As Int32
        Dim k As Int32
        Dim n As Int32

        If freq(R) = MaxFreq Then
            reconst()
        End If
        c = parent(c + T)
        Do
            freq(c) += 1
            k = freq(c)

            '
            ' Swap nodes to keep the tree freq-ordered}
            '
            n = c + 1
            If k > freq(n) Then
                While k > freq(n + 1)
                    n += 1
                End While
                freq(c) = freq(n)
                freq(n) = k

                i = son(c)
                parent(i) = n
                If i < T Then
                    parent(i + 1) = n
                End If
                j = son(n)
                son(n) = i

                parent(j) = c
                If j < T Then
                    parent(j + 1) = c
                End If
                son(c) = j

                c = n
            End If
            c = parent(c)
        Loop While c <> 0
        ' do it until reaching the root
    End Sub

    Private Shared Sub EncodeChar(ByVal c As Int32)
        Dim code As Int32
        Dim len As Byte
        Dim k As Int32

        code = 0
        len = 0
        k = parent(c + T)

        '
        ' Search connections from leaf node to the root
        '
        Do
            code = code >> 1

            '
            ' If node's address is odd, output 1 else output 0
            '
            If (k And 1) > 0 Then
                code += &H8000
            End If
            len += 1
            k = parent(k)
        Loop While k <> R
        Putcode(len, code)
        update(c)
    End Sub

    Private Shared Sub EncodePosition(ByVal c As Int32)

        Dim i As Int32

        '
        ' Output upper 6 bits with encoding
        '
        i = c >> 6
        Putcode(p_len(i), p_code(i) << 8)

        '
        ' Output lower 6 bits directly
        '
        Putcode(6, (c And &H3F) << 10)
    End Sub

    Private Shared Sub EncodeEnd()
        If putLen > 0 Then
            putc(Hi(putBuf))
            codeSize += 1
        End If
    End Sub

    Private Shared Function DecodeChar() As Int32
        Dim c As Int32
        Dim RetVal As Int32
        c = son(R)

        '
        ' Start searching tree from the root to leaves.
        ' Choose node #(son[]) if input bit = 0
        ' else choose #(son[]+1) (input bit = 1)
        '
        While c < T
            c = son(c + GetBit())
        End While
        c -= T
        update(c)
        RetVal = c And &HFFFF
        Return RetVal
    End Function

    Private Shared Function DecodePosition() As Int32
        Dim i As Int32
        Dim j As Int32
        Dim c As Int32

        Dim RetVal As Int32

        '
        ' Decode upper 6 bits from given table
        '
        i = GetByte()
        c = (d_code(i) << 6) And &HFFFF
        j = d_len(i)

        '
        ' Input lower 6 bits directly
        '
        j -= 2
        While j > 0
            j -= 1
            i = ((i << 1) Or GetBit()) And &HFFFF
        End While
        RetVal = c Or (i And &H3F)
        Return RetVal
    End Function


    '
    ' Byte manipulation helper routines
    '
    Private Shared Function Hi(ByVal X As Int32) As Int32
        Return (X >> 8) And &HFF
    End Function

    Private Shared Function Lo(ByVal X As Int32) As Int32
        Return X And &HFF
    End Function

    Private Shared Function Swap(ByVal X As Int32) As Int32
        Return ((X >> 8) And &HFF) Or ((X And &HFF) << 8)
    End Function

    Private Shared Sub InitArrayB(ByRef b As Byte())
        For i As Int32 = 0 To b.Length - 1
            b(i) = 0
        Next
    End Sub

    Private Shared Sub InitArrayI(ByRef b As Int32())
        For i As Int32 = 0 To b.Length - 1
            b(i) = 0
        Next
    End Sub
End Class

Public Class Crc
    '
    ' This class holds the routines to create and check F2BB CRC values
    ' that wrap the WinLink messages.  This CRC is different than the CRC used in
    ' the Compression class above.

    Shared CRCSTART As Int32 = &HFFFF
    Shared CRCFINISH As Int32 = &HF0B8

    Shared crcTable As Int32() = {&H0, &H1189, &H2312, &H329B, &H4624, &H57AD, _
     &H6536, &H74BF, &H8C48, &H9DC1, &HAF5A, &HBED3, _
     &HCA6C, &HDBE5, &HE97E, &HF8F7, &H1081, &H108, _
     &H3393, &H221A, &H56A5, &H472C, &H75B7, &H643E, _
     &H9CC9, &H8D40, &HBFDB, &HAE52, &HDAED, &HCB64, _
     &HF9FF, &HE876, &H2102, &H308B, &H210, &H1399, _
     &H6726, &H76AF, &H4434, &H55BD, &HAD4A, &HBCC3, _
     &H8E58, &H9FD1, &HEB6E, &HFAE7, &HC87C, &HD9F5, _
     &H3183, &H200A, &H1291, &H318, &H77A7, &H662E, _
     &H54B5, &H453C, &HBDCB, &HAC42, &H9ED9, &H8F50, _
     &HFBEF, &HEA66, &HD8FD, &HC974, &H4204, &H538D, _
     &H6116, &H709F, &H420, &H15A9, &H2732, &H36BB, _
     &HCE4C, &HDFC5, &HED5E, &HFCD7, &H8868, &H99E1, _
     &HAB7A, &HBAF3, &H5285, &H430C, &H7197, &H601E, _
     &H14A1, &H528, &H37B3, &H263A, &HDECD, &HCF44, _
     &HFDDF, &HEC56, &H98E9, &H8960, &HBBFB, &HAA72, _
     &H6306, &H728F, &H4014, &H519D, &H2522, &H34AB, _
     &H630, &H17B9, &HEF4E, &HFEC7, &HCC5C, &HDDD5, _
     &HA96A, &HB8E3, &H8A78, &H9BF1, &H7387, &H620E, _
     &H5095, &H411C, &H35A3, &H242A, &H16B1, &H738, _
     &HFFCF, &HEE46, &HDCDD, &HCD54, &HB9EB, &HA862, _
     &H9AF9, &H8B70, &H8408, &H9581, &HA71A, &HB693, _
     &HC22C, &HD3A5, &HE13E, &HF0B7, &H840, &H19C9, _
     &H2B52, &H3ADB, &H4E64, &H5FED, &H6D76, &H7CFF, _
     &H9489, &H8500, &HB79B, &HA612, &HD2AD, &HC324, _
     &HF1BF, &HE036, &H18C1, &H948, &H3BD3, &H2A5A, _
     &H5EE5, &H4F6C, &H7DF7, &H6C7E, &HA50A, &HB483, _
     &H8618, &H9791, &HE32E, &HF2A7, &HC03C, &HD1B5, _
     &H2942, &H38CB, &HA50, &H1BD9, &H6F66, &H7EEF, _
     &H4C74, &H5DFD, &HB58B, &HA402, &H9699, &H8710, _
     &HF3AF, &HE226, &HD0BD, &HC134, &H39C3, &H284A, _
     &H1AD1, &HB58, &H7FE7, &H6E6E, &H5CF5, &H4D7C, _
     &HC60C, &HD785, &HE51E, &HF497, &H8028, &H91A1, _
     &HA33A, &HB2B3, &H4A44, &H5BCD, &H6956, &H78DF, _
     &HC60, &H1DE9, &H2F72, &H3EFB, &HD68D, &HC704, _
     &HF59F, &HE416, &H90A9, &H8120, &HB3BB, &HA232, _
     &H5AC5, &H4B4C, &H79D7, &H685E, &H1CE1, &HD68, _
     &H3FF3, &H2E7A, &HE70E, &HF687, &HC41C, &HD595, _
     &HA12A, &HB0A3, &H8238, &H93B1, &H6B46, &H7ACF, _
     &H4854, &H59DD, &H2D62, &H3CEB, &HE70, &H1FF9, _
     &HF78F, &HE606, &HD49D, &HC514, &HB1AB, &HA022, _
     &H92B9, &H8330, &H7BC7, &H6A4E, &H58D5, &H495C, _
     &H3DE3, &H2C6A, &H1EF1, &HF78}

    Public Shared Function CheckCRC(ByVal buf As Byte()) As Boolean
        '
        ' Validate CRC.  Return true if CRC is valid, false otherwise
        '
        Dim crc As Int32 = FetchCrc(buf)
        Return (crc = CRCFINISH)
    End Function

    Public Shared Function CreateCrc(ByVal buf As Byte()) As Byte()
        '
        ' Return 2 byte CRC
        '
        Dim crc As Int32 = FetchCrc(buf) Xor CRCSTART
        Dim ret As Byte() = {CType(crc And &HFF, Byte), CType((crc >> 8) And &HFF, Byte)}
        Return ret
    End Function

    Public Shared Function UpdCrc(ByVal b As Byte, ByVal crc As Int32) As Int32
        '
        ' Provides an interative call to calculate CRC on the fly
        '
        Dim retCRC As Int32 = (((crc >> 8) And &HFF) Xor crcTable((crc And &HFF) Xor CType(b, Int32))) And &HFFFF
        Return retCRC
    End Function

    Public Shared Function FetchCrc(ByVal buf As Byte()) As Int32
        '
        ' Compute the Resulting CRC on the supplied data buffer
        '
        Dim crc As Int32 = CRCSTART
        For Each b As Byte In buf
            crc = UpdCrc(b, crc)
        Next
        Return crc
    End Function
End Class

