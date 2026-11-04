# Assembly of the adapted rational Levi from structural inputs

Author: Worker 1355.

This internal reduction assembles the exact, unchanged proposition
`ParabolicRadicalTorusLeviStatement.{u}` from six explicit structural
propositions: parabolic geometric solvable radical existence,
maximum-rank radical intersection, maximal-torus base change,
Borel-containing subgroup connectedness, radical-torus centralizer Levi
existence, and maximal-torus self-centralization.

`ParabolicRadicalTorusLeviReductionStatement` is their universal implication
to the published host proposition. The theorem
`parabolicRadicalTorusLevi_of_structural_inputs` proves this implication.
It does not prove any of the structural inputs or the unconditional host.

The proof first obtains the geometric solvable radical. The published
`IsParabolicSubgroup.exists_radicalTorusIntersection_of_structural_inputs`
then gives an actual commutative intersection object `S` over the original
field, its closed projection to `T`, its maximal-torus projection to the
same radical, its exact composite equation, and the full all-test
intersection equality.

The centralizer-Levi input supplies an actual rational Levi for the
radical maximal torus. The composite equation identifies its ambient
torus map with `sT ≫ t`. The published
`IsRationalLeviSubgroup.radicalIntersectionCenter` supplies the canonical
actual map `sL : S → L`, its exact factorization in `P`, and greatestness
among all closed central tori of `L`. The self-centralization input is
applied only to the original specified maximal torus of `G`.

The resulting witnesses discharge every clause of the original target
with no change to its quantifiers, predicates, or imports. All fields
lie in arbitrary universe `u`, and the range and centralizer equalities
continue to quantify over every relative test scheme. The provenance is
internal composition of the named Library interfaces; the published
centralizer-Levi statement remains a separate unproved input.
