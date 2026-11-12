# Canonical adelic Weil point topology

For arbitrary number fields `F` and `L` in a common universe with a specified
algebra `F → L`, and an affine group scheme `G` locally of finite type over
`Spec L`, `AdelicWeilRestriction.adelicPointsContinuousEquiv` constructs

`AdelicGroupPoints F (AffineWeil.groupScheme F L G) ≃ₜ* AdelicGroupPoints L G`.

Its underlying multiplicative equivalence is exactly the existing
`AdelicWeilRestriction.adelicPointsEquiv`. The theorem
`isHomeomorph_adelicPointsEquiv` proves the corresponding homeomorphism claim
directly about that fixed map. Every infinite and finite place is retained,
and both sides have their original regular-function evaluation topologies.
No reductivity, connectedness, splitting, Galois or compactness assumption
is imposed on `G`.

This is internal derived infrastructure proving the topology clause of
`AdelicWeilRestriction.NormOneComparisonStatement`. The construction composes
the finite-type Weil representing bijection with
`numberFieldAdeleTensorEquiv`, the canonical full adelic tensor equivalence.
It follows the universal continuous-family method of the affine
Weil-restriction point homeomorphism, using the full adelic
continuous-function tensor comparison. These are internal constructions
from algebraic universal properties and the original coefficient
topologies; no external reduction theorem is used.

The proof starts on the independent `AlgPoint` carriers for an arbitrary
finite-type `L`-algebra `C`. Tensor induction proves forward continuity:
each pure tensor evaluates to a fixed principal adele multiplied by the
original continuous full adelic inclusion of a coordinate evaluation.
For inverse continuity, `continuousPoint` classifies the universal
continuous evaluation family of upper-field points through the inverse of
`adeleContinuousMapTensorAlgEquiv`. Naturality of the representing bijection
and the exact continuous-function evaluation identity show that the
classified family evaluates to the inverse point map. Thus every
coordinate of that inverse is continuous.

The spectrum and affine-scheme point homeomorphisms then give
`schemePointHomeomorph` on actual relative scheme morphisms. Its
global-section formula is the canonical adelic tensor map after the Weil
representing map. The existing group equivalence has the identical formula,
by `AffineWeil.pointsEquiv_coordinates` and
`AffineWeil.coordinatePoint_changeRing`. Injectivity of the coordinate
comparison proves equality of the maps. Finally,
`affinePointsRingPointHomeomorph` identifies the actual group and scheme
point carriers by the identity on points. This retains the existing group
law and topology and packages the fixed map as the continuous
multiplicative equivalence above.

The principal-point compatibility was proved separately in
`AdelicWeilNormOneComparison`. The identification of the full normalized
rational-character kernels remains a separate obligation. This unit does
not prove the whole `NormOneComparisonStatement` or rational quotient
compactness.
