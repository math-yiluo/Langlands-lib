# Proper-source vanishing and length for represented geometric pieces

This internal derived module evaluates supplied represented geometric-lemma
intersection data and a supplied actual gluing. It uses the original condition
that every proper represented Jacquet module of the inducing representation
has zero carrier. It constructs neither the intersection data nor the gluing.

`GeometricLemmaIntersectionDatum.ProperSourceVanishingStatement` says that a
piece has a subsingleton carrier whenever its source parabolic morphism `p'`
is not an isomorphism. `properSourceVanishing` proves this proposition from
the original proper-Jacquet vanishing condition. No irreducibility assumption
on the inducing representation is needed for this implication.

`sourceJacquet_subsingleton_of_proper` applies that condition to the actual
source parabolic, its Levi and its geometric radical. Transport from the
literal Levi point image to the Levi's own points retains the carrier.
`pieceFunctor_subsingleton_of_proper` then pulls back along the supplied
conjugation isomorphism and induces to the target Levi. Pullback retains the
carrier, and normalized induction of a subsingleton carrier consists of
functions into a subsingleton. The helper
`leviInductionFunctor_subsingleton` proves this last fact directly for actual
transported normalized induction.

`representedJacquetInduction_repLength_eq_sum_fullSource` applies the generic
`IsGluedFrom.repLength_eq_sum_on` to the supplied actual gluing, discarding
all proper-source pieces by the preceding proof. The resulting sum in `ℕ∞`
is over `fullSourceIndices`, the finite set of every original index with
`IsIso p'`. Distinct indices are retained
even when their pieces are isomorphic.
`representedJacquetInduction_repLength_eq_card_fullSource` gives the exact
cardinality if every retained piece is irreducible; this is an explicit
additional premise, not proved here.

The provenance is the published definitions of represented intersection data,
actual normalized induction and Jacquet functors, together with the actual
glued-filtration length formula. These algebraic consequences supply part of
the maximal-Levi length argument. They do not establish a Weyl count,
irreducibility of the full-source pieces, detection of subquotients, a
maximal-Levi length bound, or the final unitarizable-constituent statement.
The field and carrier universes remain independent; the input carrier is in
`Type v` and induced carriers are in `Type (max u v)`.
