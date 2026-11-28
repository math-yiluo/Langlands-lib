# Pointwise detection from a strict lower leading real block

Assume exact ordinary real continuation. If the leading list has smaller
rank than both ambient lists, `realOrdinaryStrictLeadingDetection` lifts a
nonzero normalized value from the lower unequal-rank integral to an exact
ordinary test at the ambient ranks, at any point where the complementary
pair denominator is nonzero. The scale for the cut list is preserved and
the ordinary unequal-rank integral always uses the larger group first.
The measures below and at the terminal rank are supplied compatible
quotient measures. `RealOrdinaryPairHasValueAt.leadingLift` combines this
comparison with the two cases at and above the comparison rank.

Use the smooth preimages of the two lower coefficients and the compact
leading restriction in the cut slot. The rank-raising comparison gives
a finite expansion using the terminal paired smooth tests. If every exact
terminal test vanishes at the given point, continuity and compact-finite
extraction make every normalized value in the expansion vanish there.
The expansion then normalizes the lower integral by the upper pair factor
with zero value at the point. Multiplication of the given nonzero lower
value by the complementary denominator gives another normalization by
the same factor. The two normalizations agree by their common right
half-plane identity, so the upper tests cannot all vanish there.

The normalized comparison implements the strict lower case of Proposition
14.3 in §14.2, pp. 104–106, using the column factorization of Proposition
6.1, pp. 41–42, and the rank transfer of Lemma 14.1, pp. 106–107.
[H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), author-posted
edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf#page=104)

The registered source is `jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
