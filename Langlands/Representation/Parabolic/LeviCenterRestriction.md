# Restricting a Levi central character to the ambient center

This internal construction supplies the topological full-center part of the
central-character bridge for normalized parabolic induction. It applies to an
arbitrary commutative ring and block shape. For its continuous maps, the ring
has a topology making it a topological ring. The two complex representation
carriers have independent universes, also independent of the ring universe.
Zero carriers and rank zero are allowed.

`GeneralLinear.BlockShape.diagonalScalarToCenter` sends a unit `a` to the tuple
of scalar matrices `(a I_(n_i))_i`, with its membership certificate in the full
Levi center. It is the restriction of the published `blockScalarToCenter` to
constant tuples. `leviEmbedding_diagonalScalar` proves that the actual block
diagonal embedding sends this tuple to the ambient scalar matrix `a I_n`.
The proof uses the published matrix-entry formula for block scalars.

Every element of the ambient center is a scalar matrix by Mathlib's
`Matrix.GeneralLinearGroup.center_eq_range_scalar`, including rank zero.
Consequently it belongs to the block parabolic.
`centerToParabolic` packages this actual inclusion as a homomorphism.
`centerToLeviCenter` then applies the actual diagonal-block projection. Its
centrality certificate follows by writing the ambient element as a scalar,
using the section identity for the projection, and observing that its image
is the common scalar tuple. `centerToLeviCenter_scalar` records that formula.

`centerToLeviCenterContinuous` uses the subgroup topologies throughout.
The inclusion from the ambient center into the parabolic is continuous because
its composite with the parabolic inclusion is the continuous ambient-center
inclusion. Composing it with the published continuous Levi projection and
restricting the codomain to the Levi center proves the asserted continuity.
No continuity of an inverse scalar parametrization is assumed.

For a representation `σ` of the actual product Levi, a supplied
`c : UnitaryCentralCharacter σ`, and an ambient representation `ρ`,
`unitaryCentralCharacterOfLeviScalar` constructs
`UnitaryCentralCharacter ρ` under the explicit compatibility identity

```text
ρ(a I_n) w = c.character((a I_(n_i))_i) • w.
```

Its full-center character is exactly
`c.character.comp (B.centerToLeviCenter R)`. The inverse image of the supplied
open kernel under the proved continuous map is open. Its values have norm one
by the supplied Levi character datum. Writing an ambient central element as a
scalar proves the scalar-action field from the compatibility identity.
`unitaryCentralCharacterOfLeviScalar_character` records the exact pullback
formula. No smoothness or nontriviality of the ambient representation is
needed for this construction.

The provenance is internal: these maps and their correctness proofs are
deductions from the published block embeddings and projections, the full-center
and block-scalar constructions, and the definition of
`UnitaryCentralCharacter`. No additional literature theorem is asserted.
For actual normalized induction, its prescribed scalar-action identity remains
the separate `Parabolic.NormalizedInductionCentralClause` proof obligation.
This module supplies no induction scalar-action calculation, Haar comparison,
coefficient estimate, or temperedness conclusion.
