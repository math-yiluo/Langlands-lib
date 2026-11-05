# Relative norms on rational points

For a compatible field tower `k → L → M`, coefficient points of the actual
base change `G_L` are identified multiplicatively with the original coefficient
points of `G`. The map is projection from the scheme pullback; restriction of
scalars leaves the test spectrum unchanged. This identification commutes with
coefficient extension and every relative `M/L` automorphism.

For an affine commutative group scheme and finite Galois `M/L`, injectivity of
coefficient extension and the full conjugate-product formulas identify the norm
of `G_L` with `relativeNorm` on the original coefficient carriers.
`relativeRationalNorm` transports that relative norm to the existing rational
points of the two direct base changes `T_M` and `T_L`. If both `L/k` and `M/k`
are also finite Galois, its composite with the `L/k` rational norm is the `M/k`
rational norm, by the already proved coefficient norm transitivity.

This is internal infrastructure for the nested splitting-field comparison in
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Lemma 2.5.12,
printed pp.89–90 (PDF pp.120–121). No valuation or independence conclusion is
assumed or asserted here.
