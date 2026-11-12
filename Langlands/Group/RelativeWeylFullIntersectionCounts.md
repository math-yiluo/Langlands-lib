# Counting full-source minimal representatives

This is an internal finite counting construction for the geometric length
argument of Renard, *Représentations des groupes réductifs p-adiques* (9 July
2026), VI.5.4, printed pp.173–174 / PDF pp.179–180. The construction generalizes
the existing coatom occurrence count to any injectively labelled family of
target subsets with the source cardinality.

For a finite Coxeter system, `fullIntersectionRepresentatives cs J I` is the
finite set of minimal representatives in `W_J \ W / W_I` with full source
intersection `intersectionSubset cs J I w = I`.
`sum_fullIntersectionIndicators` says that a bijective enumeration of the
minimal representatives counts this set exactly, by summing one for a full
source intersection and zero otherwise. It is stated for any additive
commutative monoid with one and its natural casts.

`sum_card_fullIntersectionRepresentatives_le` sums these finite-set
cardinalities over an arbitrary finite label type. The target-subset map is
explicitly injective and preserves the source cardinality. Sending each
occurrence `(a,w)` to `(target a,w)` embeds its finite sigma set into the
existing `fullIntersectionPairs cs I`, because minimality, cardinality and
full source intersection are retained. This proves the cardinal bound with
no loss of occurrences or assumption that different labels are equal.

These are combinatorial helpers only; no representation length or Jacquet
detection conclusion is asserted here.
