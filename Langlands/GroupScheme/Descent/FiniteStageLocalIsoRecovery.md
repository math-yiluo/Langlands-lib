# Exact recovery of finite-stage local isomorphisms

This internal extension of `FiniteStageIso` identifies the local family of
an exact finite model with the original local family after extending back
to the larger field. The fields and schemes lie in an arbitrary universe
`u`. No algebraicity, separability or finiteness premise is needed beyond
the supplied `IsoModel`.

Let `e` be an actual isomorphism between two ground-field group schemes
after extension from `k` to `Ω`, and let `D : IsoModel k Ω e`. Its chosen
finite intermediate field is `E`. The stored recovery equation compares
`e` with the pullback of `D.iso` using the direct-to-iterated base-change
comparisons.

`IsoModel.recovery_projection` composes that equation with the projection
from the iterated pullback to the group over `E`. The published projection
formula for the comparison and the pullback map formula identify the
result with the commutative square formed by the actual maps
`G_Ω → G_E`, `H_Ω → H_E`, `D.iso` and `e`.

`IsoModel.localIso_refine` states equality of the full local families:
refining `D.localIso` along the actual field-cover map `Spec Ω → Spec E`
gives `LocalGroupIso.ofBaseChangeIso e`. The proof evaluates on every
relative scheme `T`, every cover point `T → Spec Ω` and every group point.
The pullback universal property identifies the lift at the finite stage
with the projection of the lift over `Ω`. The preceding commutative square
then identifies their images. The published local-family extensionality
theorem concludes equality, including every multiplicative equivalence
and its naturality.

The provenance is internal: these lemmas combine the exact finite-model
recovery, tower projection, local-family refinement and pullback point
interfaces already in the Library. They construct no initial isomorphism,
quasi-split model, adjoint quotient or inner discrepancy. Their role is to
make exact finite-stage recovery available to all-test discrepancy descent.

The definition selected for this contribution is `IsoModel.refinedLocalIso`.
It constructs the natural local equivalences over `Spec Ω` by refining the
finite model's actual family along `Spec Ω → Spec E`.
`IsoModel.refinedLocalIso_eq` identifies this constructed object with the
family of the specified original isomorphism, using `localIso_refine`.
This equality uses the stored exact recovery equation, rather than a choice
of an unrelated isomorphism over the larger field.
