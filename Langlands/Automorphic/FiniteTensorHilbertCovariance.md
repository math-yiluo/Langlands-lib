# Covariance of actual automorphic tensor Hilbert maps

This internal specialization uses a supplied genuine finite tensor presentation
`P` and invariant positive form `b`, with independent number-field and local
carrier universes, exactly as in `FiniteTensorHilbertEmbedding`.

`separatedHilbertEquiv_completedOperator` proves that the completed separated
tensor equivalence intertwines the source completed operator at a finite-local
matrix with the original global completed operator at its actual local insertion.
It applies `InvariantPositiveForm.completedEquiv_comp_completedOperator` to the
actual `P.localEquiv`, its surjectivity and the definitionally preserved pullback
form. The target completion is exactly that of `b` because restriction keeps the
positive core. No tensor presentation or positive form is asserted to exist;
no group-variable continuity, decomposition or spectral occurrence is claimed.

`sliceHilbertEmbedding_completedOperator` gives the corresponding covariance for
any fixed tail, including zero. It applies the generic actual-image completed
isometry law to the actual subtype inclusion and its pulled-back positive form.

For an explicitly nonzero complementary tensor,
`factorSliceHilbertEquiv_completedOperator` intertwines the extracted local
factor completion and the actual slice completion. It specializes the generic
completed-equivalence covariance law to `P.sliceEquiv`, using its actual
surjectivity and definitionally preserved pullback form.

`factorHilbertEmbedding_completedOperator` composes the factor-to-slice and slice
covariance formulas. Congruence under the slice embedding gives the first step;
its covariance gives the second. Thus the factor's extracted completed action
agrees with the original global completed action at the actual local insertion
on the factor's genuine embedded image.

`sliceHilbertIntertwiner` packages the actual completed slice inclusion as an
intertwiner into `b.completedRepresentation` restricted along the actual finite
local insertion. Its linear map is `sliceHilbertEmbedding.toLinearMap`; the
intertwining equation is the proved slice covariance law, packaged by
`LinearMap.ext`. Its value is therefore definitionally the slice embedding.
No nonzero-tail premise is needed for this construction, including the zero
slice.

The unit is an internal construction from the generic completion/restriction
covariance tools and the preceding actual tensor completion maps. It retains
the original global completed action at the inserted local subgroup. Invariant
range packaging, a general Hilbert tensor product decomposition, canonical local
positive forms, spectral occurrence and archimedean globalization remain separate
work.
