# Strong segment heads from actual consecutive words

Authors: Worker 320 (proof and original draft), Worker 495 (dependency and
complete-signature verification and submission).

The theorem `consecutiveIntegralCuspidalWordSegmentHead` proves the named
proposition with arbitrary supplied p-adic field and topology, independent
universes, and actual saturated smooth representations.

Set `z = a-(l-1)` and twist the given actual supercuspidal `A` by
`|det|^z`. Twist that object again by the decreasing integers
`l-1, ..., 0`. The class twist addition law and elementary cast arithmetic
identify these actual factors with the labels `a, ..., a-(l-1)`.
`integralCuspidalJacquetWord_occurrence_of_labeling` recovers their actual
tensor occurrence from the supplied word.

The published `glCuspidalTensor` proves that this tensor is irreducible
and Levi cuspidal. The published
`exists_inductionInjection_of_cuspidalOccurrence` uses admissibility,
the whole cuspidal Jacquet quotient, and actual first adjointness to
embed `π` into the decreasing induction. Its inducing factors are
definitionally the decreasing segment factors of the chosen base.

The published individual-segment existence theorem supplies a strong
special head, and `IsSegmentHead.nonempty_equiv_of_down_subrepresentation`
identifies `π` with it. Transport through that actual equivalence gives the
strong head relation, retaining the equality of all irreducible quotient
kernels.

The auxiliary `consecutiveIntegralCuspidalWordSegmentHead_of_rank` accepts
an arbitrary ambient rank. The actual word's degree identity supplies
`l * m = n`; transporting the representation along that equality reduces
to the exact theorem above. The returned equality is retained in the strong
head conclusion, so it can be used for coarse factors of a larger product.

This is an internal composition of published lower results and the
accompanying actual-word realization helper. It assumes the consecutive
word and does not construct it or prove analytic classification.

The recursive project import audit at Library base
`a5dff2ff93bd3637a67ee8847f67f811efc82f01` contains 802 modules, including
the two new modules in this contribution. All 800 imported Lean and Markdown
pairs match that base. The target pair and its 57-module import closure are
unchanged. The imported inputs include the actual cuspidal tensor theorem,
cuspidal constituent quotient detection, first adjointness, and the
individual-segment strong head and decreasing socle. The closure contains
no use of segment analytic classification, multisegment exhaustion, ordered
strong-head existence, quotient coverage, tempered block uniqueness,
square-integrable classification or exhaustion, regular exhaustion, or
proof successors of those conclusions. The general analytic predicates and
lower support adapters imported by adjointness do not supply any of those
excluded conclusions.
