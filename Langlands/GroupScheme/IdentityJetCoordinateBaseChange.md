# Actual ambient jet coordinate sections under change of base

This internal naturality result uses the actual cartesian jet square from
`IdentityJetBaseChange` and the actual global ambient-coordinate sections
from `IdentityJetCoordinates`.

Let `G/S` have affine structure morphism, let `b : T → S` be arbitrary,
and let `j : G.total → Spec B` be an actual scheme morphism. For opens
`U` of `S` and `V` of `T` with `V ≤ b⁻¹(U)`,
`baseChangeSectionsRingMap` is actual pullback of functions along the
actual map of identity neighborhoods. `baseChangeMap_preimage` supplies
its open condition from the cartesian projection square.

`jetCoordinateMap_baseChange` computes the image of an ambient coordinate:
it is the same coordinate pulled back by the actual composite
`G_T.total → G.total → Spec B`. The proof is composition of actual
function pullback, using the inclusion factorization of the actual jet map.

`vanishesAtIdentity_baseChange` preserves actual identity vanishing by
the identity-section base-change formula. Consequently
`quotientCoordinates_baseChange` computes pullback of the prescribed
global quotient-coordinate sections, restricted to any compatible
pair of opens. It reduces to representatives in `B` and the coordinate
function formula. The statement concerns actual scheme-function
pullback; it does not silently replace it with a chosen module isomorphism.
