# The finite group on all actual scheme components

Author: Worker 1107.

This internal derived construction uses the published
`AlgebraicallyClosedComponentProof` and `RationallyRepresentedComponents`.
Its provenance is transport of the already constructed finite group through
the now proved surjectivity onto all actual scheme components. No external
structure theorem is used.

Let `k : Type u` be an algebraically closed field of any characteristic and let
`H` be an actual smooth affine group scheme over `Spec k`.
`AlgebraicallyClosedComponents H` is a type synonym for
`ConnectedComponents H.X.left`, including every actual scheme component.
The carrier itself is defined over any field; the group construction assumes
algebraic closedness, smoothness and affineness.

`allComponentEquiv` forgets the membership witness from the subtype of rationally
represented components. Its injectivity is subtype injectivity; its surjectivity
uses the published `rationalComponentEmbedding_bijective_of_isAlgClosed`.
Transport through its inverse gives the group structure on the full carrier,
and injectivity into the finite represented-component group proves finiteness.
`allComponentMulEquiv` is the resulting group equivalence. Its forward map is
the underlying component, and its inverse has that same underlying component.
Composing with the published quotient comparison gives
`allComponentQuotientEquiv : H(k)/H^0(k) ≃* AlgebraicallyClosedComponents H`.
Its value is exactly `rationalComponentEmbedding`.

`allComponentOfPoint` is a surjective group homomorphism from actual rational
sections to all actual components. Its underlying map is `pointComponent`.
The multiplication, identity and inverse equations identify the constructed
operations with the components of the corresponding operations on rational
sections. These formulas and surjectivity determine the operations on the
entire carrier, independently of the chosen rational representative.

For an actual group-scheme homomorphism `f : H ⟶ H'` between smooth affine
groups over `k`, `allComponentMap f` transports the published
`representedComponentMap`. `allComponentMap_apply` proves that its underlying
function is the continuous map on the actual scheme's connected components.
The identity and composition laws hold as equalities of group homomorphisms.

Now let `k` be any field and `L` an algebraically closed extension in the same
arbitrary universe `u`, and let `H` be smooth affine over `k`. Write `H_L` for
the actual base change. `allComponentConjugate k L H sigma` transports
`representedComponentConjugate` through `allComponentMulEquiv H_L`.
`allComponentConjugate_apply` identifies its function on every component with
`coefficientComponents`, the published permutation induced by the actual
semilinear scheme automorphism. Its one and multiplication laws give
`allComponentGaloisAction : Aut_k(L) →* MulAut (AlgebraicallyClosedComponents H_L)`.
Thus the actual coefficient permutations preserve the constructed group law.
`allComponentConjugate_naturality` proves that the group homomorphisms induced by
actual maps over `k` intertwine these actions.

`allComponentFixedSubgroup` consists of components fixed by every coefficient
automorphism. Its membership condition is equivalent to fixedness under every
actual scheme-component permutation.
`allComponentFixedEquiv` restricts the comparison equivalence to the represented
and full fixed subgroups, with inverse given by the inverse comparison.
`allComponentQuotientFixedEquiv` consequently identifies the ordinary
rational-component quotient's fixed subgroup with the full fixed subgroup.
`allComponentBaseChangeToFixed` is the injective homomorphism from rationally
represented components over `k` to this full fixed subgroup over `L`.
Its component equation is the published rational-quotient field-extension map
followed by its actual-component embedding. Its injectivity is inherited from
the published map into represented fixed components.

No algebraicity, separability, normality, perfection or characteristic assumption
is imposed on `L/k`; `L` is required to be algebraically closed. The construction
does not assume `k` is algebraically closed in this extension part.
This constructs a finite abstract group on all actual scheme components and a
coefficient action. It constructs no component-group scheme or sheaf quotient,
no descent or surjectivity onto the fixed subgroup, and no topology or
continuity result for the action. The quotient used in the comparison is the
ordinary rational-point quotient.
