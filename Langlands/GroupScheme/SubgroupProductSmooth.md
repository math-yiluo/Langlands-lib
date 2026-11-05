# Smooth subgroup products from actual intersections

Workers 1554 and 133. This is internal infrastructure derived from the published
subgroup-product orbit, exact coset fibers, and fpqc descent constructions.

`QuotientCell.smooth_of_smooth_subgroup` works over any base scheme. A flat,
surjective, quasi-compact morphism from an actual group scheme, with the
right-coset fibers of a monomorphic smooth subgroup on every relative scheme
test, is smooth. The exact fibers identify its self-pullback with the product
of the group and the subgroup, using `multiplication_isPullback`. The
projection from that product is smooth, and fpqc descent gives the conclusion.
The morphism need not be a group homomorphism.

`smooth_subgroupProductMap_of_surjective_of_smooth_intersection_algClosed`
applies over an algebraically closed field. Both source groups and the
ambient group are smooth and affine; the second subgroup map is closed.
It assumes scheme surjectivity of the actual multiplication map and
smoothness of the actual scheme-theoretic intersection. Inverting the
second factor identifies multiplication with the published two-sided
product orbit. Scheme surjectivity lifts rational points, so the orbit is
flat and quasi-compact by `orbitMapFaithfullyFlat`. Its exact stabilizer
is the diagonal copy of the actual intersection. The preceding descent
lemma proves smoothness of the orbit map, and the inversion isomorphism
transfers smoothness to `subgroupProductMap`.

`smooth_subgroupProductMap_of_surjective_of_smooth_intersection`
is an internal proof-producing definition with the same hypotheses over
an arbitrary field in universe `u`.
It extends scalars to `AlgebraicClosure k` in that same universe.
Smoothness and affineness of the three groups, closedness of the second
subgroup map, and smoothness of the actual intersection persist under
base change. The pullback square for the original multiplication and
the canonical product comparison carry scheme surjectivity to the
base-changed multiplication. The algebraically closed criterion proves
that map smooth. The published
`smooth_surjective_subgroupMultiplication_of_fieldExtension` then
descends smoothness along the fpqc field extension. The existing
`subgroupMultiplication` and `subgroupProductMap` are definitionally
the same actual relative morphism.

The generic lemmas impose no characteristic restriction and no
connectedness, normality, or commutativity hypotheses on the three
groups. They require smoothness of the group structure morphisms,
not smoothness of either supplied subgroup homomorphism.

This criterion does not prove either surjectivity or intersection smoothness
for a derived cover and a maximal torus. Those structural inputs remain
separate obligations of the target proof.
