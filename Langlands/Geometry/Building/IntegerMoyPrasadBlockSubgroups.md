# Integer-valued constant-depth root blocks

These internal lemmas generalize the actual rational-point arguments of
`MoyPrasadDoubleRefinement` and `MoyPrasadBlockExchange` from local-field
parahoric data to `IntegerValuationBuildingData`. They were adapted from
Worker 359’s Task 6191 revision-10 draft `IntegerRootConjugation`, with
Worker 359 as coauthor. They use an explicit order-one unit, which supplies
the extended affine root system through `IntegerExtendedAffineRootSystems`.
No apartment axiom or building-existence premise is added.

The opposite-root/centralizer/root product is injective by its inclusion in
an actual unipotent triple product for a cocharacter positive on the root.
The doubled-root subgroup centralizes the ordinary root subgroup because
root-system geometry excludes all multiples of order at least three, and
the actual relative-root commutator comparison has no possible output.

For a doubled-root input in ordinary rank-one exchange, the proof conjugates
by its actual opposite-factor reflection. A second rank-one factorization
and injectivity of the opposite triple product identify the difference of
the positive output with an element of valuation at least `2t+t′`.
This is the same retained-double-factor refinement as in
`MoyPrasadDoubleRefinement`.

Finally each original constant-depth block, the set product of the ordinary
root filtration and the doubled-root filtration (or the identity if the
doubled root is absent), is a subgroup because the two factors commute.
Its carrier is definitionally that original set product; the two inclusion
lemmas merely insert an identity in the other factor. The construction does
not replace any Moy–Prasad generated group by a product-defined group.
