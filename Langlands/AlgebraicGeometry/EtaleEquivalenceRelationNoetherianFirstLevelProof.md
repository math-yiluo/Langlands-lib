# A Noetherian first level of a separated étale equivalence relation

`Langlands.AlgebraicGeometry.etaleEquivalenceRelationNoetherianFirstLevel`
proves the unchanged Library proposition
`EtaleEquivalenceRelationNoetherianFirstLevelStatement.{u}` for arbitrary
universe `u`. Its inputs are exactly an étale equivalence relation `E`,
affineness of `E.U`, and a closed immersion
`(t,s) : E.R → E.U × E.U`.

The implemented proof closes the presentation-level descending induction
for Stacks Project, Proposition 70.8.1, Tag 07SU, in the registered source
`stacks-noetherian-approximation-2026-11-01`. It uses the published finite
tuple presentations and their stratification, the affine open-extension
construction, and the actual cross-cover quotients. This proof works with
schemes and cartesian morphisms of their étale equivalence relations
throughout.

First, the closed immersion into the product of the affine object scheme
with itself makes `E.R` affine, by `E.isAffine_relation`. An affine scheme
is separated over the integers, so the source morphism `E.s` is separated.
Thus the additional geometric instances used by the tuple construction
follow from the two stated hypotheses.

Set `N = E.tupleLengthBound`. The proved descending-induction constructor
`E.nonempty_affineFiniteTypeFirstLevel_of_tupleTail_systems` needs, for
each `p < N+1`, a finite type cartesian system on the actual next-threshold
restriction of the tail starting at `p`, given an affine finite type first
level of the higher tail starting at `p+1`. The theorem supplies this
step with
`E.nonempty_finiteTypeCartesianSystem_tupleTailNext N p le_rfl`.
That constructor uses the higher tail's first level to descend its actual
cross-cover action, descends the two invariant affine quotient covers for
the action and its diagonal pair action, and compares their quotients with
the actual next-threshold relation. At the final threshold the length
bound makes that restriction empty.

The induction constructor starts with the empty tail at `N+1`. At each
step it applies the proved affine open-extension and actual-tail recovery
construction. After reaching the zero tail, it transfers the resulting
first level along its actual affine étale chart to `E`. Consequently it
returns an `AffineFiniteTypeFirstLevel E`, containing an actual relation
`E₀`, a cartesian comparison from `E`, affine object and arrow schemes,
and an object scheme of finite type over the chosen terminal scheme
`Spec ℤ`.

Finally, the existing Noetherian instance for
`AffineFiniteTypeFirstLevel` makes `E₀.U` Noetherian: finite type over the
integers implies local Noetherianness, and affineness supplies
quasi-compactness. The proof returns `E₀`, the object and arrow components
of its comparison, its cartesianness proof, and these three geometric
properties. It adds no hypothesis asserting an approximation statement.
