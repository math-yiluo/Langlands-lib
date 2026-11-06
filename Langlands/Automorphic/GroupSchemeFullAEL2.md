# Full almost-everywhere cuspidal L2 subrepresentation

This construction uses the actual positive-central rational quotient,
its existing norm-one transported Haar measure, and every actual proper
rational parabolic radical. Separate almost-everywhere absolute convergence and
vanishing remain part of the cusp condition. The standing structural
`ParabolicDynamicStatement`, connected reductivity, affine locally finite-type
number-field scope, central split torus and injective finite-index character
restriction remain explicit.

The raw-function auxiliary submodule imposes precisely the separate AE period
convergence and vanishing conditions, with norm-one Haar as the translation
measure. It imposes no ambient measurability or L2 condition. Its linear laws
follow from pointwise linearity of the actual descended integrands and the
Bochner integral on convergent inputs.

The actual quotient-period representative-congruence theorem transfers this
condition between strongly measurable functions equal almost everywhere for
the positive quotient measure. The proof pulls equality through the exact
measure-preserving norm-one comparison and identifies the canonical normalized
radical measures without a scalar factor. Applying it to the chosen Lp
representatives of zero, addition and scalar multiplication constructs
`fullAEL2CuspidalSubmodule`, whose carrier is definitionally the original
`fullAEL2CuspidalLocus`.

For every ambient adelic element, including elements outside the norm-one
subgroup, the existing quotient homeomorphism intertwines positive right
translation with right multiplication by its explicit `normOneProjection`.
Applying this equality to the actual radical-orbit points proves the
pointwise period-integrand translation identity. The separately assumed
right invariance of norm-one Haar transfers both AE conditions along this
multiplication. Representative congruence then transfers the result to the
chosen Lp representative of the original quotient L2 action.

This constructs `fullAEL2CuspidalSubrepresentation` with exactly the original
full carrier and `fullAEL2CuspidalRightAction` by restriction. Its norm
preservation follows from the ambient L2 isometry.
`fullAEL2CuspidalToLp` is the subtype inclusion as an intertwining map.
The construction proves neither closedness nor completeness of this
submodule; these require the separate all-parabolic closedness theorem.

The implementation is an internal construction using the full-carrier
convention of Getz–Hahn (6.20)–(6.21), printed page 168 / PDF page 182, and the
compact-period setup in Section 9.2, printed pages 242–246 / PDF pages 254–258,
with the complete October 2026 errata. It retains actual subgroup quotients,
the original probability normalizations and positive right-orbit convention.
It does not identify the full locus with the image of smooth cusp functions,
establish density, discharge ambient right invariance, or prove spectral claims.
