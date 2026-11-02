# Decreasing block words forced by a least global word

`Langlands.Classification.MinimalIntegralCuspidalBlockWords` is an internal
derived prerequisite for extracting segment factors from a least actual
cuspidal Jacquet word. It retains arbitrary primes, the supplied p-adic field
and topology, independent field and carrier universes, and actual smooth
complex representations on carriers in `Type (max uF uV)`.

An actual external tensor of coarse representations `X i` occurs as a
subquotient of a normalized upper Jacquet module of `π`. Each `X i` is
irreducible and is an actual subquotient of an inner normalized upper cuspidal
product. The input cuspidal factors have rank-indexed classes given by integer
real-power twists of one actual supercuspidal representation `A`. Each inner
integer list is weakly decreasing. Let the reference word be their ordered
concatenation. Assume that no realized word which permutes this reference
word is lexicographically smaller than it. Then each original inner word is
an actual `IntegralCuspidalJacquetWord` of its corresponding coarse factor.

The reference word need not separately be assumed to occur: the stated
minimality condition and constituent hypotheses force the conclusions. No
irreducibility, admissibility, finite length, or analytic condition is imposed
on `π`. Positive ranks of the coarse factors are supplied by `BlockShape`;
there is no additional positive-total-rank hypothesis. All occurrences are
actual subquotients, with repeated labels and their multiplicities retained.

The provenance is internal composition. Supercuspidal embedding, uniqueness
of support, and first adjointness supply a realized permutation of each
inner label list, as expressed by `IntegralCuspidalConstituentWord`. Actual
Jacquet refinement and tensor-subquotient reassembly concatenate these words
to a realized word of `π`. A decreasing list is lexicographically greatest
among its permutations. Comparing the first unequal block, whose length is
fixed by permutation, shows that any unequal block would make the global
concatenation smaller. Hence every chosen block is its reference block.

This file states the prerequisite and supplies no Lean proof. It does not
extract a whole Jacquet quotient or induction embedding, identify a special
segment constituent, construct an initial integral twist line, or establish
analytic square-integrability or segment classification.
