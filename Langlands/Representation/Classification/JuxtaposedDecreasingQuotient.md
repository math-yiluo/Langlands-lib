# The decreasing induction surjects onto the juxtaposed socle product

This internal supporting construction gives an actual surjective intertwiner
from the decreasing induction of a concatenated segment to a two-block product
of supplied strong segment socles. It explicitly assumes
`SegmentZelevinskyConstituentExistence`; it does not prove that proposition or
the exact juxtaposed case of Proposition 4.6.

Let `ρ` be a cuspidal datum of positive rank `r`, represented by the supplied
supercuspidal representation `A`. The datum `d` has total degree `(q + l) * r`
and exactly two factors. Its first segment has base `ρ.twist l` and length `q`;
its second has base `ρ.twist 0` and length `l`. The supplied `HasSegmentSocles`
hypothesis specifies actual strong socles on these blocks. No irreducibility
of the product is assumed. In this situation
`exists_surjective_from_decreasing` provides a surjective intertwiner from
`segmentInducedDown A.obj (q + l) ρ.rank_pos` to `d.induced`.
`decreasingUnionQuotient` selects such an actual map, packaged in a subtype with
its surjectivity proof.

The proof adapts Worker 1032's increasing-embedding draft, with the quotient
construction and decreasing-exponent argument supplied by Worker 167. Choose
representatives of the two segment bases. The existing conditional
`IsSegmentSocle.decreasingHeadQuotient` gives a surjection from each block's
decreasing induction onto its supplied socle. The proved exactness of normalized
product induction makes the resulting outer product map surjective.

The full uniform shape with `q + l` blocks of size `r` is refined into the two
segment shapes. The lexicographic flattening index has values `k` on the first
block and `q + k` on the second. Consequently its decreasing exponent
`q + l - 1 - flatIndex` equals the first segment's exponent `q - 1 - k` plus `l`,
or the second segment's exponent `l - 1 - k`, respectively. These equalities are
proved in natural numbers before passage to real exponents. The representative
and twist equivalences in `JuxtaposedRefinementTools` identify these factors
with the two blockwise decreasing factor families. Ordered normalized-product
regrouping supplies an actual isomorphism from the full decreasing induction
to the product of the two decreasing inductions. Composing that isomorphism
with the surjective outer product map proves the claim.

The construction preserves independent field and representative-carrier
universes `uF` and `uV`. Regrouping starts at carrier universe `uV`; the blockwise
induced representations and product map use `max uF uV`. The imports are lower
block, twist, constituent and normalized-induction infrastructure. The only
unproved representation-theoretic input is the explicit individual-segment
constituent-existence hypothesis. No linked-product classification, reverse
product, commutation, geometric lemma or derivative theorem is used.
