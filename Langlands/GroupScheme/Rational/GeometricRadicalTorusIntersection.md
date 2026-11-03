# Canonical intersections with a supplied geometric solvable radical

Author: Worker 1441.

`solvableRadicalTorusIntersection f r hr` constructs the canonical commutative
scheme-theoretic intersection of an actual map `f : T → P`, with `T`
commutative, and a supplied solvable radical `r : R → P`. The construction
uses the radical's closedness to provide the monomorphism required by
`commutativeSubgroupIntersection`. It does not require `T` to be a torus
and does not assert that the resulting intersection is a torus.

The first and second projections are the original pullback maps to `T`
and `R`. Their composites in `P` agree, and the common range is exactly
`range f ∩ range r` on every scheme over the field, including nonreduced
and nonaffine tests. The first projection is closed, by pulling back the
closed radical inclusion. These construction and comparison laws need
no structural theorem about reductive groups or parabolics.

`isMaximalTorus_solvableRadicalTorusIntersectionSnd_of_geometric` takes a
connected reductive group `G`, a smooth closed subgroup `j : P → G`
that is geometrically connected, and a specified maximal torus
`t : T → G` factoring as `f ≫ j = t`. It also takes an actual geometric
solvable radical `r : R → P`. It proves that the second canonical
projection is a maximal torus of this same radical representative,
conditional on the two named propositions
`MaximalRankRadicalTorusIntersectionStatement` and
`MaximalTorusBaseChangeStatement`.

The proof extends the actual maps to `AlgebraicClosure k`. The proved
`IsConnectedReductive.baseChange_toAlgebraicClosure` supplies ambient
reductivity; smoothness is stable under pullback, and geometric connectedness
is supplied explicitly. Forward maximality follows from the base-change
statement. The second conjunct of the geometric radical predicate identifies
the supplied base-changed radical. The maximum-rank intersection statement
then gives a full intersection representative with a maximal-torus map
to that radical. Closedness of `f` follows by factoring the closed maximal
torus through the closed subgroup `j`.
`isMaximalTorus_commutativeSubgroupIntersectionSnd_of_baseChange_representative`
compares the supplied representative with the canonical pullback and
reflects maximality to the original field. Thus the construction does not
descend a choice of geometric torus: its original-field object is the
canonical intersection itself.

`IsParabolicSubgroup.exists_radicalTorusIntersection_of_structural_inputs`
specializes this to a parabolic and exposes the actual original-field
intersection witnesses, both required geometric properties, the composite
equation and the full range equality. Its third structural hypothesis is
`BorelContainingSubgroupConnectedStatement`. Parabolicity supplies an actual
Borel factor over the algebraic closure. The connectedness statement applied
to this factor and the connected reductive ambient group proves geometric
connectedness of `P`. The preceding descent theorem gives maximality; the
canonical projections give all remaining conclusions.

This is internal derived infrastructure from the published pullback,
representative-comparison and base-change APIs and the explicit named
structural propositions. It does not prove any of those propositions.
It also does not construct a solvable radical, a rational Levi, a largest
central subtorus, or an unconditional proof of
`ParabolicRadicalTorusLeviStatement`. The arbitrary-field host target is
unchanged. All fields and algebraic closures here lie in the same arbitrary
universe.
