# Character adapters for finite degree-zero Brauer induction

Worker 1787 supplies internal derived infrastructure for the unchanged finite
degree-zero Brauer statement. No generation conclusion is assumed or asserted.
All groups here have arbitrary, independently chosen universes.

`extend S f` extends a complex function on a subgroup by zero. `ind S` is the
integer-linear normalized conjugation sum, using the published
`ClassFunction.induced` convention. `ind_apply` states its explicit dependent
sum, and `ind_character` identifies it with the trace character of the actual
finite-dimensional induction `induceRep`. `virtualCharacter_induce` extends this
comparison to the genuine split representation group by writing each virtual
class as a difference of actual classes.

`characterSpan G` is exactly the image of `degreeZeroBrauerSpan G` under the
actual virtual-character map. It is not a substitute ambient representation
group. `generator_mem` realizes every normalized induced rank-one difference in
this image. `ind_ind` transports a function through nested subgroup induction
using the image subgroup and its canonical equivalence with the original inner
subgroup. Its proof uses the published normalized-sum transitivity theorem,
with an explicit comparison on the support subgroup. `ind_mem` then proves
preservation of `characterSpan` by induction on the original genuine span.

For a surjection π, `sum_comp_surjective` counts every fiber using its equivalence
with the kernel. `card_comap_surjective` obtains the inverse-image subgroup
cardinality by combining this count with subgroup index identities.
`ind_comap` proves that induction from the inverse-image subgroup of S commutes
with inflation along π. The factor given by kernel cardinality in the sum
cancels the same factor in the subgroup normalization. `pullback` is the
integer-linear composition operation, and `pullback_mem` uses this formula to
prove preservation of `characterSpan`, again by induction on the genuine span.

These are internal comparisons derived from definitions and the published
actual induction-character theorem and normalized induction transitivity API.
They do not invoke ordinary or degree-zero Brauer generation, monomiality,
or faithfulness, and have no independent external-source assertion.
