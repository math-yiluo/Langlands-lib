# Rank transport and finite-block gamma assembly

This internal contribution supplies total-rank transport for actual normalized
product induction and the conditional theorem
`Langlands.RankinSelberg.gammaMultiplicativity_of_twoBlock`.
Worker 20 authored this module. Its provenance is a derivation from the imported
Library constructions and certificate relations; it asserts no new external
analytic result.

`rankCastRepresentation h σ`, for an equality `h : a = b`, substitutes that
equality in a representation of `GL_a(F)`. The vector space, its additive group,
and its complex module structure are retained. The construction does not
precompose the representation by a nontrivial ambient matrix permutation.

`normalizedProductRankCastEquiv T C h σ` identifies the rank-substituted
normalized product induced from `C` with the actual normalized product induced
from `C.rankCast h` and the same ordered factor family. `BlockShape.rankCast`
retains the block lengths and sizes and changes the proof of their total.
Eliminating `h` reduces the construction to the reflexive representation
equivalence. The field universe and factor-carrier universe are independent.

The conditional theorem has precisely these two premises:

- `TwoBlockGammaMultiplicativityStatement.{uF,uV,uW}`;
- `TwoBlockGammaMultiplicativityStatement.{uF,uV,max uF uW}`.

Its conclusion is the existing
`GammaMultiplicativityStatement.{uF,uV,uW}`, including existence of a certified
rational function for every block pair and the product certificate for the
actual canonical normalized upper product induction. The field, test carrier,
and original factor carrier have independent universes. The induced tail has
carrier universe `max uF uW`, explaining the second premise.

The proof is induction on the number of ordered blocks. The empty family
contradicts the positive total rank. For one block, applying the first two-block
premise to a duplicated copy of that representation supplies a factor
certificate for the original pair. `singleBlock_gamma_iff` then transports this
certificate to the actual normalized singleton induction. No separate
factor-existence premise is used.

For at least two blocks, the tail has positive total rank. The induction
hypothesis supplies certificates for its original factors and for their product
against its actual normalized induction. The published
`normalizedProductWhittakerType` proves full Whittaker type for that induced
tail, including the admissibility, finite-generation and functional-line
clauses. The rank-transport equivalence identifies the tail shape presentation
with the successor-rank presentation required by that theorem.

The published `headTailProductFactors` consists of the original first factor
lifted by `ULift.{uF}` and the actual normalized induction of the remaining
ordered factors. Full Whittaker-type invariance under representation
equivalence supplies the head and tail hypotheses for the second two-block
premise. A private shape adapter eliminates the equality between the outer
size function and its positive successor-rank form before applying that
premise. This retains the actual induction, rather than identifying different
dependent factor families informally.

Representation-equivalence invariance of
`IsPadicSymmetricGammaFactor` returns the head certificate to its original
carrier. The same invariance and uniqueness of symmetric gamma certificates
identify the outer tail factor with the product supplied by induction.
`headTailProductInductionEquiv` transports the outer product certificate to the
original actual normalized product. Its first/tail grouping preserves the
original ordered coordinates and positive-half-modulus normalization.
`Fin.cons`, the two-element product formula and the successor product formula
then give the desired original block family and its product.

All uses of smoothness follow from the supplied full Whittaker-type hypotheses.
The character, supplied self-dual Haar measure, canonical field topology,
positive-rank scope, both rank orders and reducible full-type inputs remain
those of the existing statements. The imported symmetric certificate transport
and uniqueness lemmas handle both rank orders.

This is a conditional assembly result. Neither two-block premise is proved in
this module. Its publication does not establish the closed
`GammaMultiplicativityStatement` required by the parent task.
