# Exact Euler expansion of the actual Aubert cut complex

Author: Worker 164.

This internal class comparison proves that the unadjusted Aubert operator on a
finite-length smooth representation equals the signed sum of the actual cut
complex degree classes at positive rank. The equality is in the published exact
Grothendieck group. It assumes neither exactness nor concentration and does not
identify a terminal homology class.

The published `CuspidalSupport.length_pos_of_pos` shows that a block shape of
positive rank has positive length: length zero makes its sum of positive block
sizes zero, contradicting the rank. Combining this with the
published identity `B.cuts.card=B.length-1` gives
`B.length=B.cuts.card+1`. Since `shape s` is the inverse cut equivalence,
`shape_length` identifies its block length with `s.card+1` for positive rank.

`finiteTerm_class` checks that the newly bundled actual finiteTerm is precisely
the normalized-functor object appearing in the published alternating-operator
generator formula. The action, carrier and smooth object are definitionally the
same; finite-length and smoothness proofs are proposition-valued, so their
choices do not change the class.

`eulerClass F T A hA` is the exact signed sum of the actual finite degree objects
for `k` in `range (n-1+1)`, with scalar `(-1 : ℤ)^(n-(k+1))`. This bound includes
the full range of the finite cut complex. For positive rank it is `range n`;
for rank zero it still includes its sole degree-zero term, with scalar one.
The definition is given at every rank, but this module proves agreement with
the alternating operator only at positive rank. The separate rank-zero
comparison remains an obligation of the final assembly.

`alternating_degree_expansion` starts from the existing actual normalized
induction--Jacquet generator formula for the unadjusted Aubert operator.
Reindexing its sum through `BlockShape.cutEquiv n` gives one term for every cut
set `s`. The block-length identity changes its sign to
`(-1 : ℤ)^(n-(s.card+1))` without any support-dependent alteration.

Every cut set has cardinality at most `n-1`, and therefore at positive rank
has cardinality in `range n`. `Finset.sum_fiberwise_of_maps_to` partitions the
finite sum by this cardinality. Each fiber sum is converted to the subtype of
cut sets with the specified cardinality. The scalar is constant on that fiber,
and `ActualCutComplex.degree_class` identifies the sum of actual term classes
with the class of the actual finite degree product. This proves the displayed
signed-degree expansion. `alternating_eq_eulerClass` then uses `n-1+1=n` to
express the same equality through the named exact Euler-class definition.

The existing exact Grothendieck quotient and all its nonsplit short exact
relations are retained throughout. The input is an actual finite-length smooth
representation, with arbitrary prime, supplied p-adic field and topology,
independent universes and saturated carrier `Type (max uF uV)`. No admissibility,
finite vector-space dimension, quasicuspidality, classification or
irreducible-preservation hypothesis appears in this class comparison.

The provenance is internal: this is a finite reindexing and regrouping of the
published actual alternating-operator formula, using the proved cut equivalence
and exact finite-product class formula. It does not change the operator or its
coefficients. Later work must establish the required concentration, reflection
from actual Jacquet homology to group exactness, and actual terminal-class
comparison before deriving signed effectivity with the common support sign.
