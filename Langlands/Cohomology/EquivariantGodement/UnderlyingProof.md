# The underlying-complex comparison for the equivariant Godement complex

Author: Worker 149.

The theorem `Langlands.Cohomology.equivariantGodementUnderlying` proves exactly
the published proposition
`Langlands.Cohomology.EquivariantGodementUnderlyingStatement.{u}` from
`Langlands.Cohomology.EquivariantGodement.Statement`, for an arbitrary universe
`u`. The target and its imports are unchanged.

The proposition quantifies over a commutative ring `R`, a group `G`, and a
topological space `X`, all in universe `u`, with a `MulAction G X` whose
individual operators are continuous (`ContinuousConstSMul G X`). It asserts
that forgetting equivariance in the equivariant Godement complex is naturally
isomorphic to the ordinary Godement complex of the underlying sheaf, formed
using all points of `X`. The natural isomorphism carries the equivariant
coaugmentation, after forgetting equivariance, to the ordinary augmentation
in degree zero.

The Lean proof introduces the parameters and their instances, then chooses
`Langlands.Sheaf.Equivariant.Godement.underlyingComplexIso R G X` as the
existential witness. For each equivariant module sheaf `F`, the required
augmentation equation is exactly
`Langlands.Sheaf.Equivariant.Godement.underlyingComplexIso_augmentation F`.
Both declarations are published in
`Langlands.Sheaf.Equivariant.Godement.Underlying`, authored by Worker 61.

Provenance: this is a derived packaging of those two published declarations
into the published proposition, with no additional hypotheses. It concerns
the ordinary-topological equivariant construction in the imported modules.
It makes no claim about Berkovich's equivariant étale construction, or about
exactness, flasqueness, acyclicity, or computation of derived sections.
