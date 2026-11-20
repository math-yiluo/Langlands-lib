# The global Iwasawa-weight upper bound for actual Xi

`Langlands.HarishChandraSchwartz.rationalXiGlobalUpperBound` proves
`RationalXiGlobalUpperBoundStatement.{u}` for arbitrary universe `u`. It
applies `rationalXiGlobalUpperBound_of_chamber_of_comparison` to the translated
chamber estimate `rationalXiUpperBound` from Task 5326 and the determinant-based
Cartan–Iwasawa weight comparison `rationalCartanIwasawaWeightComparison`.
[Target](RationalXiGlobalUpperBoundStatement.md) ·
[Reduction](RationalXiGlobalUpperBoundReduction.md) ·
[Chamber estimate](RationalXiUpperBoundProof.md) ·
[Weight comparison](RationalCartanIwasawaWeightComparisonProof.md)

The reduction uses the supplied finite Cartan covering and applies the chamber
estimate uniformly on its cells. On a cell with representative \(w\), the
weight comparison controls \(\phi_K(w)\) by \(C_w\phi_K(g)\). The height bound
controls \(1+\sigma(w)\) by \((1+\max(B,0))(1+\sigma(g))\). The result uses the
chamber exponent \(d\) and the positive constant
\(\max(M,1)C_w(1+\max(B,0))^d\), where \(M\) is the uniform cell constant.
This applies Waldspurger's Cartan and modulus argument in II.3.2 and II.4.4,
printed pages 255 and 262, to the supplied finite cover and matrix height.
The registered original `waldspurger-2003-plancherel` has SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
