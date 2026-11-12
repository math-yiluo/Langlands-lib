# Fixed-model curve-place stages and original local Weil factors

This internal construction identifies each enlarged arithmetic stage of a
fixed Weil model over principal curve S-integers with the product of its
original upper local factor points. Arbitrary finite extensions, including
inseparable extensions, are allowed.

Let `k` be a finite field, `K` a global function field over `k`, and `L/K`
a finite extension with the specified compatible `k`-algebra structures.
Choose `s` with `K` finite-dimensional over `k(s)` and a nonzero element
`t` of the associated chart ring. The lower initial support is
`curvePlacePrincipalExceptional k K s t`; the upper coefficient ring uses
its full preimage in `L`. Let `T` enlarge the lower initial support.

Let `X` over the upper ring be quasi-separated and of finite type, and
assume that its Weil restriction `W` to the lower ring is algebraic.
For the stage homeomorphism also assume that the lower initial support
is nonempty and that `W` is separated and of finite type. These supply
the lower arithmetic stage coordinate bijection.

`upperField` is the original completion at each upper place above each
lower coordinate. `upperFieldAlgHom` is the identity at field coordinates
and the original integral inclusion at integer coordinates. The original
completion embeddings give continuous scalar multiplication and finite
dimensionality; completeness gives their module topology. The published
local-field theorem gives henselianity for the original separately
normalized norms.

`fieldTensorData` supplies the original completed-field tensor equivalence
with the fixed lower coefficient action. Equality of the original algebra
maps identifies this action with the native action on the completion.
`fieldPointMap_isHomeomorph` applies the finite-type tensor field comparison,
with case analysis reducing its field instances to the original completion
structures.

`factorPointHomeomorph` applies the integral-to-field comparison uniformly
to field and integer coordinates. Its lower tensor decomposition is exactly
`CurvePlacePrincipalSIntegerFixedLevelWeil.tensorEquiv`; its field row is
`fieldTensorData`. The original coefficient square commutes by the definitions
of the completion maps and integral inclusions. The resulting homeomorphism
has the original field-valued topology on the lower Weil factor and the
product of those on the upper factors. Its component formula is exactly
`completedTensorSpaceWeilRestrictionPointMap` for that fixed-level tensor.

`levelPointHomeomorph` composes the original lower stage coordinate
homeomorphism, the product of these factor homeomorphisms, and the
homeomorphism from the nested product to the product indexed by pairs of
lower coordinates and upper places above them. Both directions of the last
map are continuous by coordinate evaluation. The component theorem retains
the original tensor map after coefficient change along
`CurvePlacePrincipalSIntegerFixedLevelWeil.levelFactorAlgHom`, the original
enlarged-level projection.

The provenance is internal composition of actual arithmetic tensor
decompositions, complete-local-field results, the integral comparison, and
space stage coordinates. No separability, scheme, projectivity or smoothness
hypothesis is imposed on `X`. This unit does not regroup upper factors into
their arithmetic stage or establish the final adelic homeomorphism.
