# Descent of integration through a positive averaging map

Worker 112 implements the algebraic and Riesz-representation step used in
quotient integration. This is an internal construction from an averaging map
and explicit proved properties of that map. It does not prove those properties
for a subgroup and does not by itself prove `CompatibleMeasureExists`.

`descendPositiveLinearMap` starts with a surjective real linear map `P : A → B`
between ordered real modules and a positive linear functional `I` on `A`.
It requires `ker P ⊆ ker I` and a nonnegative preimage for every nonnegative
element of `B`. Mathlib's quotient universal property descends `I` to `A/ker P`,
and its first isomorphism theorem identifies that quotient with `B`. Nonnegative
preimages prove positivity. The evaluation formula at `P a` is proved from these
two quotient constructions, and surjectivity proves uniqueness of the descended
positive linear functional with those values.

`measureOfPositiveAveraging` specializes this construction to compactly supported
real continuous functions on a Borel topological space `X` and a locally compact
Hausdorff Borel space `Y`. Its input measure `μ` on `X` need only be finite on compact sets. The
positive functional on `X` is the actual `integralPositiveLinearMap μ`, not an
arbitrary proposed quotient functional. Applying `RealRMK.rieszMeasure` to the
descended functional constructs a measure on `Y`. Mathlib gives regularity and
the exact identity `∫ P f = ∫ f`. If one ambient test integral is nonzero, the
same identity proves that the constructed measure is nonzero.

Surjectivity and Mathlib's extensionality theorem for regular measures prove
uniqueness among regular measures satisfying the integration formula on averages.
If a homeomorphism of `Y` intertwines averaging with an integral-preserving
transformation of the source test functions, the pushforward measure has the
same formula. Regularity of that pushforward and uniqueness prove that the
homeomorphism preserves the constructed measure.

This is a derived internal implementation of the last functional step in
Folland's sufficiency proof of Theorem 2.51, rather than a transcription of a
separately named theorem. The algebraic route is Mathlib's quotient-of-kernel
construction. The downstream group application must supply the actual averaging
map, its surjectivity and positive lifting, its kernel calculation, and a
nonzero test integral. Equivariance and invariance of source integrals, and the extension to
complex-valued integration, remain obligations in the group application. No second countability or sigma compactness is used.

Source context: Gerald B. Folland, *A Course in Abstract Harmonic Analysis*,
second edition (2015), section 2.6, Theorem 2.51 sufficiency proof, printed page
63 / PDF page 76. Registered source
`folland-2015-abstract-harmonic-analysis-second`, SHA256
`c82467bfa77428c32d3e1a5d1cbdc11129511e0c61da2f9d8fbc717776b9e542`.
The original was read. The proof uses the pinned Mathlib implementations of
`Submodule.liftQ`, `LinearMap.quotKerEquivOfSurjective`,
`PositiveLinearMap.mk₀`, and `RealRMK.rieszMeasure`.
