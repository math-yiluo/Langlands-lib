# Regrouping Arthur's truncation with the relative partition

For a continuous left `G(F)`-invariant function on `G(𝔸)` and compact-factor data for the same `K`, the truncation sum has one term for each standard parabolic and each rational
coset. The relative Siegel partition at the chosen representative of an outer
coset gives a finite sum equal to one. The proof inserts this factor and reindexes
outer and relative right cosets using the equivalence in `ArthurRightCosetTower`.
The hatted cutoff and constant term are invariant under the rational points of
the outer parabolic. The partition factor is invariant under the smaller
parabolic. These invariances ensure that the reindexed sum evaluates each
product at the chosen representative of the smaller coset.

This is the first regrouping in the proof of Arthur 2005, Proposition 13.2,
printed p. 71 (PDF p. 83), using the relative partition (8.1).

For the regrouping displayed before (13.7), apply the expansion of the product of the relative and
hatted chamber cutoffs in `sigma` and interchange the two finite
parabolic sums. The inner sum of signed constant terms is
`alternatingConstantTerm`, the factor defined in (13.7). The coefficient of each such term is the
truncated Siegel indicator times the corresponding sigma cutoff. For
fixed parabolic indices, the defining expansion of sigma expresses the
coefficient as a finite sum of terms with finite support on the rational
cosets, so the resulting coset sum has finite support.

The relative partition follows from the Siegel covering and reduction
conditions. `arthurTruncationSigmaExpansion` combines these steps with the
regrouping for every parameter above the resulting regularity threshold.
