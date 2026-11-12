# Geometric torsion coordinates from ample existence and the cube theorem

This internal assembly constructs residue-linear coordinates on actual
geometric torsion conditional on two explicit geometric propositions:

- `Langlands.GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement`;
- `Langlands.GroupScheme.FieldCubePullbackStatement`.

Neither proposition is proved by this module. The construction does not
complete the unconditional `GeometricTorsionRankStatement` proof task.
Its provenance is the composition of the published Library results named
below; it introduces no new assertion from external literature.

`fieldTorsionCardinality_of_ample_and_cube` proves the published
`FieldTorsionCardinalityStatement` from these two inputs. For an actual
abelian scheme `B` over an algebraically closed field `K`, ample existence
provides an actual ample line bundle `L` on `B`. The published theorem
`AbelianScheme.finrank_multiplication_eq_of_ne_zero` then computes the
native rank of actual multiplication by `n` as `n^(2*g)`. That theorem
symmetrizes `L`, derives its multiplication-pullback identity from the
cube theorem and applies the proved numerical polarized finite-flat rank
theorem. The relative dimension and nonzero image of `n` in `K` are the
existing hypotheses of the field-cardinality statement.

The published `natCard_level_eq_multiplicationFinrank_at_unit` identifies
the cardinality of the existing `GroupScheme.Tate.Level` with this native
rank at the unit point. A point of `Spec K` exists because `K` is a field.
The assembly composes these equalities. It supplies no numerical rank,
degree, basis, substitute module or assumed field-fibre equivalence.

`geometricTorsionRank_of_ample_and_cube` applies the published
`geometricTorsionRank_of_fieldTorsionCardinality`. That reduction applies
the field count at every positive divisor of `n`, constructs the actual
torsion coordinates by finite abelian group classification, and promotes
the additive equivalence to a linear one for the already installed
residue actions. It also transfers the global unit to the point field,
preserves smooth relative dimension under actual base change and
transports actual torsion along the additive pullback comparison. Its
conclusion is the entire unchanged relative target, with both geometric
premises still explicit.

`geometricTorsionLinearEquivOfGeometry` chooses the linear equivalence
from the existence conclusion of that conditional theorem using
`Classical.choice`. Its target is exactly the existing
`GroupScheme.Tate.Level A.toGrp (Over.mk s) n`, with its existing
`ZMod n` action. The choices at different levels and geometric points
have no asserted compatibility.

The construction is polymorphic in the scheme universe and covers every
positive invertible level, including `n = 1`, and every specified smooth
relative dimension, including `g = 0`. It needs ample existence only over
algebraically closed fields; arbitrary-field ample existence and descent
are not additional obligations for this assembly. An unconditional proof
still requires published proofs of the two explicit geometric inputs.
