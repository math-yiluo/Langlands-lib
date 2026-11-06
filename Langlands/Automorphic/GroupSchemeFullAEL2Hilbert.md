# The Hilbert structure on the original full AE cuspidal carrier

This internal construction reuses the exact all-parabolic closedness
theorem `groupSchemeParabolicL2Closedness` and the existing
`fullAEL2CuspidalSubmodule`. It keeps its full carrier, rather than
replacing it by the closure of a continuous or smooth image. The
number-field and actual connected reductive group, affine locally
finite-type scope, structural `ParabolicDynamicStatement`, central split
torus, injective finite-index character restriction and norm-one right
Haar invariance remain explicit.

`fullAEL2CuspidalClosedSubmodule` packages that same submodule with the
closedness conclusion of the actual theorem.
`FullAEL2CuspidalHilbertSpace` abbreviates the original submodule. Its
norm, topology and complex inner product are those inherited from the
actual positive-quotient `Lp ℂ 2` space, with its unchanged canonical
measure. The completeness instance follows from closedness in this
complete ambient space. No finite volume premise or new completion
quotient is introduced.

`fullAEL2CuspidalInclusionLI` is the original subtype inclusion as a
complex-linear isometry. Its underlying linear map equals the existing
full-AE intertwining inclusion. Mathlib's Hilbert orthogonal projection
then constructs `fullAEL2CuspidalOrthogonalProjection` from the whole
actual L2 space into the original full cusp carrier. Its operator norm is
at most one and it fixes every vector of that carrier.

`fullAEL2CuspidalAmbientProjection` is the same projection with ambient
codomain. Its values lie in the full cusp submodule, and its fixed vectors
are precisely the original `fullAEL2CuspidalLocus`.

`fullAEL2CuspidalRightTranslate` bundles each existing restricted right
action as a surjective complex-linear isometry, with inverse the action
of the inverse adelic element. Stability under both that element and its
inverse identifies the image of the cusp submodule under the ambient
right isometry with the same submodule. Mathlib's
`LinearIsometry.map_starProjection` then proves that the ambient
orthogonal projection commutes with the original right action.
Subtype extensionality gives equivariance of the cusp-valued projection,
and `fullAEL2CuspidalProjectionIntertwiner` bundles that same projection
as an intertwining linear map. No continuity of the action in the adelic
element is asserted here.

Composing this projection intertwiner with the original faithful
`fullAEL2CuspidalToLp` inclusion is the identity intertwiner of the same
full cusp representation, by the projection's fixed-vector identity.

The provenance is the named actual all-parabolic theorem followed by the
pinned Mathlib closed-submodule completeness and orthogonal-projection
APIs. This is an internal Hilbert-space construction, with the source
conventions and hypotheses already recorded in the imported actual-period
and closedness modules. It makes no smooth or continuous density claim,
no identification of cuspidal with discrete spectrum, and no spectral or
trace assertion.
