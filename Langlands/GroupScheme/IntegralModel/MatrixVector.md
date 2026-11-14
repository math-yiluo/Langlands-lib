# Integral vector models with arbitrary basis matrices

For a domain `R` with fraction field `K`, the integral model `matrixVector`
has polynomial vector group over `R` as its underlying group. Its generic
identification with the fixed polynomial vector group over `K` is given by
an invertible square matrix `B`. The model is affine, flat, of finite type,
smooth, and has geometrically connected fibres.

The section-coordinate formula identifies its integral-point image exactly
as the vectors `B * a`, where the column `a` has coefficients in `R`.
The proof uses the canonical coefficient-ring section coordinates and the
matrix-map formula on all scheme tests, followed by actual base change.

For two such basis matrices `B` and `C`, an integral matrix `M` with
`C * M = B` over `K` gives an integral-model map extending the generic
identity. Over a local domain, every extension of that same generic
identity has smooth, connected, unipotent scheme-theoretic kernel on its
special fibre. Generic rigidity identifies it with the explicit matrix
map. The general matrix-kernel theorem applies to its reduction, without
any assumption on the rank of that reduction.

This is an internal construction from polynomial vector groups and linear
algebra, supporting the depth-dependent integral bases in Kaletha–Prasad,
*Bruhat–Tits theory: a new approach* (2023), Section C.2, printed
pp.697–698 (PDF pp.728–729). It does not identify these lattices with a
supplied apartment filtration or prove the full C.5.3 statement.
