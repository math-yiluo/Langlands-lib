# Integral tensor Weil comparison by induced field topologies

This internal unit transfers a tensor Weil point homeomorphism over fields
to the corresponding comparison over coefficient rings whose point
topologies are induced through maps to those fields. The coefficient rings
can be completed valuation rings. It retains algebraicity and the field
comparison as explicit inputs.

For an algebraic space `X` over a commutative ring `B` and a `B`-algebra
map `f : A → K` to a topological field,
`isInducing_changeRing_fieldValuedPointTopology` states that coefficient
change `X(A) → X(K)` is inducing. The source topology is the field-valued
topology along `f`; the target is the field-valued topology along the
identity of `K`. This follows from functoriality of the field-valued
point map and composition of induced topologies.

The tensor data consist of commutative rings `R`, `B`, and `C`, a field
`C'`, a finite family of commutative rings `D i`, and a matching family
of fields `D' i`. Both lower rings are `R`-algebras. Each upper ring has
its specified lower-ring algebra structure and its specified original
`B`-algebra structure. The given tensor algebra equivalences
`C tensor_R B ≃ product D i` and `C' tensor_R B ≃ product D' i` must
take `1 tensor b` to the original image of `b` in each factor.
The specified coefficient maps `f : C → C'` and `g i : D i → D' i`
are respectively `R`-linear and `B`-linear and satisfy
`g i (algebraMap C (D i) c) = algebraMap C' (D' i) (f c)`.
The fields have specified topologies.

For an algebraic space `X` over `B`, assume its Weil restriction over
`R` is algebraic. Also assume that the original tensor factor map over
`C'` is a homeomorphism for the original field-valued topology of the
Weil space and the product of the original field-valued topologies on
`X(D' i)`. The imported
`isHomeomorph_completedTensorSpaceWeilRestrictionPointMap` supplies
this field input when its explicit norm, module-topology, henselian,
algebraicity, and geometric hypotheses are available.

`WeilRestrictionTensorTopology.integralPointHomeomorph` identifies the
Weil space's `C`-points with the product of `X(D i)`. The source has the
field-valued topology along `f`; each target factor has the field-valued
topology along `g i`. Its forward components are exactly the original
`completedTensorSpaceWeilRestrictionPointMap` over `C` and the `D i`.
The final theorem states the homeomorphism property for that map.

The implemented proof uses the arbitrary-ring tensor point equivalence
from `SpaceWeilRestrictionTensorPointEquiv`. Coefficient change on the
source is inducing by the first lemma; the product of the upper
coefficient changes is inducing by `IsInducing.piMap`. Original
coefficient naturality identifies their square with the tensor maps.
Composing the lower inducing map with the assumed field homeomorphism
and cancelling the upper inducing map proves that the integral tensor
equivalence is inducing, hence a homeomorphism.

This provenance is internal composition of existing tensor point
naturality, the ring-level bijection, and induced topology properties.
No injectivity of the coefficient maps is assumed or needed for this
argument. General Weil representability, the field comparison's
geometric hypotheses, arithmetic specializations, and the adelic endpoint
are not proved in this unit.
