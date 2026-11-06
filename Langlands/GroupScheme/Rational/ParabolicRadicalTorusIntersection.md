# Original-field torus intersections with a supplied geometric radical

Author: Worker 1441.

`RadicalTorusIntersection f r` is a data type bundling a commutative group
scheme `S`, actual maps `S → T` and `S → R`, closedness of the first map,
maximal-torus status of the second, their composite equality in `P`, and
the full all-test intersection equality.
`IsParabolicSubgroup.radicalTorusIntersection` constructs this bundle with
the canonical pullback object and its original projections.

`IsParabolicSubgroup.exists_radicalTorusIntersection` takes a connected
reductive group scheme `G` over an arbitrary field `k`, an actual parabolic
`j : P → G`, a specified ambient maximal torus `t : T → G`, its actual factor
`f : T → P` with `f ≫ j = t`, and a supplied geometric solvable radical
`r : R → P`. It constructs a commutative group scheme `S` over `k` with
actual projections `sT : S → T` and `sR : S → R`. The first is closed, the
second is a maximal torus of this same radical representative, and their
composites in `P` agree. The common range is the full intersection
`range f ⊓ range r` on every relative test scheme, including nonreduced
and nonaffine tests.

The constructor specializes the published
`IsParabolicSubgroup.exists_radicalTorusIntersection_of_structural_inputs`.
Every named structural premise of that adapter is supplied by a published
proof:

- `maximalRankRadicalTorusIntersection` supplies
  `MaximalRankRadicalTorusIntersectionStatement`.
- `maximalTorusBaseChange` supplies `MaximalTorusBaseChangeStatement`.
- `borelContainingSubgroupConnectedStatement` supplies
  `BorelContainingSubgroupConnectedStatement`.

The adapter obtains geometric connectedness of the parabolic from its
actual Borel factor over the algebraic closure. It extends the specified
maximal torus and geometric radical to that field, applies the maximum-rank
intersection theorem, compares its representative with the base change of
the canonical pullback, and reflects maximality to `k`. The constructor
uses the adapter's resulting representative and
`isMaximalTorus_commutativeSubgroupIntersectionSnd_of_representative` to
obtain maximality for the canonical second projection. Closedness of `f`
follows from `f ≫ j = t` and the closedness of the two embeddings into `G`.
The bundled object is `solvableRadicalTorusIntersection f r hr.1`, with
its canonical projections. Closedness, composite equality and the all-test
range equality come from that original-field pullback. The existential
theorem reads off the bundle's fields. No chosen geometric intersection
object needs to descend.

The accompanying
`isMaximalTorus_solvableRadicalTorusIntersectionSnd` applies to any smooth
geometrically connected closed subgroup of `G` containing the specified
ambient maximal torus. It supplies the first two published proofs to
`isMaximalTorus_solvableRadicalTorusIntersectionSnd_of_geometric`; geometric
connectedness is an explicit hypothesis in this more general version.

This pair is derived internal construction infrastructure from those
published proofs and the canonical intersection adapters. The constructor
and theorems have no unproved structural-theorem premise. They retain the supplied
`IsGeometricSolvableRadical r` hypothesis; this pair does not construct the
radical or a rational Levi and does not prove
`ParabolicRadicalTorusLeviStatement`. No splitness, perfectness, characteristic
or rational-point density condition is imposed. The field and its algebraic
closure lie in the same arbitrary universe `u`.
