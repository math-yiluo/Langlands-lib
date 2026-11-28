# Associativity of the total multiplication

The fibre product `G3` represents triples of points of `Gl` over `S`.
The open of triples whose two consecutive pairs lie in `mulOpen` is
represented by `Triples.T3`, via `j`. Its image contains the generic
points of `G3`. On this open, the two composites of `mulBar` become the
two sides of `mulG_assoc`. Since `G3` is reduced and `Gl` is separated
over `S`, `assoc` holds on `G3`.

For a pair with defined original product, `mulPts_in_chart` says that
multiplying the first point in a chosen chart by the second in the
original chart gives their original product in the chosen chart. For a
section chart, this follows from the formula for the product with that
section and total associativity. These identities implement the
associative multiplication used in BLR, *Néron Models*, §5.3 Lemma 8,
pp. 127–128.
