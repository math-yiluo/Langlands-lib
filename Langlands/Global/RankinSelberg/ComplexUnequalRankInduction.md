# Induction on the ranks in the complex local functional equation

Two recurrence inputs suffice for the exact unequal-rank local functional equation. `ComplexEqualCanonicalSuccessorStatement` gives the canonical normalized equal-rank equation for the standard trace character at the next rank, given the normalized adjacent pair. `ComplexUnequalNormalizedRankGapStepStatement` increases the larger rank with the smaller rank fixed, using the normalized equation at the preceding unequal pair.

The first induction starts from the normalized rank-one Tate equation. `complexAdjacentFromEqual` goes from that equal-rank input to the adjacent pair, and the assumed equal-rank successor followed by `complexEqualNormalizedFromCanonical` gives the next equal rank. With every adjacent pair available, the second induction applies the rank-gap step to obtain the other unequal pairs.

Each exact intertwiner value belongs to the corresponding Whittaker model. Applying the normalized equation to these values and then using `complexLocalUnequalFromNormalized` gives the integrability, holomorphy, meromorphic continuation and functional equation in the published proposition.

The two recurrence statements are hypotheses of this reduction. [Jacquet, *Archimedean Rankin–Selberg integrals*, Sections 8–10](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
