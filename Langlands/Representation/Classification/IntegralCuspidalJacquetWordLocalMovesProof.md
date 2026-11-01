# Conditional local moves for actual integral cuspidal Jacquet words

`integralCuspidalJacquetWordLocalMoves` proves the proposition
`IntegralCuspidalJacquetWordLocalMoves` with independent field and carrier
universes. The three representation-theoretic propositions in its implication
telescope remain premises: actual adjacent Jacquet interchange, nonadjacent
two-supercuspidal product irreducibility, and repeated-factor triple transfer.

For each supplied irreducible, admissible, composition-finite-length actual
object `π`, the proof applies the three word lemmas from
`IntegralCuspidalJacquetWordAdapters`. The first applies the unlinked-pair
lemma, reversing the equalities excluded by the statement so that they match
the helper's orientation. The second and third apply the lower-repeat and
upper-repeat lemmas directly. Those helpers reconstruct actual occurrence
after the supplied transfer, with every outside factor retained. The upper
case keeps both alternatives as a disjunction.

The supporting module explains its derivation from actual rank-indexed class
equalities and actual tensor subquotients, its published twist-injectivity,
equal-rank commutation and binary-product bridge inputs, and its remaining
conditional transfer premises. This wrapper introduces no further
representation-theoretic assertion. In particular, it neither constructs an
initial realized word nor proves any of the three supplied propositions.
Segment extraction, strong heads and analytic classification remain separate.
