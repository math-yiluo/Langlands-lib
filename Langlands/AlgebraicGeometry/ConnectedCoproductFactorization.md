# Actual factorization of connected-source scheme coproduct maps

Author: Worker 57.

This derived helper constructs a factorization of any morphism from a connected
scheme to a coproduct of schemes through an actual summand. For an arbitrary
universe `u`, the source is `T : Scheme.{u}`, the index is `I : Type u`, and
`X : I → Scheme.{u}`. The only geometric assumption is `ConnectedSpace T`,
which includes nonemptiness. No local Noetherianity, reducedness, flatness,
finite index or separate inhabitance of `I` is assumed.

`connectedHom_factor_coproduct` composes the original scheme morphism's
continuous underlying map with the inverse of
`AlgebraicGeometry.sigmaMk X`. This homeomorphism identifies the underlying
space of the actual scheme coproduct with the topological disjoint union.
Mathlib's `Continuous.exists_lift_sigma` factors that continuous map through
one summand. Applying the forward homeomorphism proves that the underlying
range of the original morphism is contained in the range of the actual
`Sigma.ι X i`. This summand inclusion is an open immersion.
`IsOpenImmersion.lift` therefore constructs a scheme morphism into the
original summand, and `IsOpenImmersion.lift_fac` proves that its composite
with the summand inclusion equals the original morphism.

`connectedCoproductIndex` chooses an index from this proved existence result,
and the entry `connectedCoproductLift` chooses the corresponding actual scheme
morphism. `connectedCoproductLift_comp` is the chosen witness equation, with
a reassociated simp equation as well. The resulting equality is an equality
of scheme morphisms, including their structure-sheaf maps. Nilpotents in the
source and targets are retained.

The provenance is internal: the proof combines the pinned Mathlib coproduct
homeomorphism, connected topological factorization and the universal lift
along an open immersion. It introduces no new literature assertion or moduli
hypothesis. It is infrastructure for extending residual-index uniqueness
arguments to connected scheme tests; it supplies no Shimura representability,
rigidity, etaleness or cover theorem.
