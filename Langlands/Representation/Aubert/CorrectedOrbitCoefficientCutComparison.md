# Common actual orbit coefficients across cuts

Author: Worker 194.

This internal prerequisite compares actual source-cut orbit coefficients with
one common flattened Jacquet quotient. It retains the actual source Jacquet
projection in the coefficient map.

`intersectionSource_eq_of_intersectionTarget_eq` is a group-theoretic fact:
if the target intersection is the whole target subgroup, inverse conjugation
of that target is contained in the source subgroup. Their source intersection
therefore equals that inverse conjugate. `wholeTarget_flattened_eq` applies
this fact to the actual block Weyl groups. The published identification of
a source refinement's flattened Weyl group with the source-side intersection
then shows that all source refinements with whole-target intersection flatten
to the same standard block shape. Injectivity of block Weyl groups recovers
the actual block shape equality. No minimality hypothesis is needed for this
individual equality; the whole-target Weyl intersection and actual source
intersection refinement equalities are explicit.

`jacquetShapeCongr` is equality transport of actual Jacquet carriers. Its
class formula follows by eliminating the block-shape equality.
`cutOrbitCoefficientCommonEquiv` composes the actual nested coefficient to
flattened Jacquet equivalence with this equality transport. Its original-vector
formula sends the nested class of the source Jacquet class of `v` to the
common Jacquet class of `v`.

`cutOrbitCoefficientCommonEquiv_cutMap` proves that the genuine cross-cut
coefficient projection becomes the identity under these identifications.
Every nested coefficient class is represented by a source Jacquet vector,
and every such vector is represented by an original vector. On that vector,
the actual cut projection preserves its class and both common-coefficient
maps give exactly the same common Jacquet class. Thus the equality holds
for all actual nested coefficient classes, without a choice of representatives.

The provenance is internal: elementary subgroup conjugation and published
actual intersection, quotient and representative formulas. The module proves
linear coefficient comparisons only. It does not identify compact induction
with evaluation at the identity, assemble the graded cut diagram, or prove
signed effectivity. Arbitrary rank, including zero, and independent field
and representation universes are retained.
