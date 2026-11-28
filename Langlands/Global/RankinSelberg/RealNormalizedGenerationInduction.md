# Pointwise induction for real normalized generation

The right bounds on the real parts of the Gamma poles give two disjointness
results for the pair denominators. For a single right block, the denominator
of the left list after removing its smallest-exponent block cannot vanish
where the reflected dual denominator of the removed block vanishes. For
multiple right blocks, the same reflected dual denominator has no common
zero with the denominator of the pair formed by the full left list and the
largest-exponent right block.

The proof uses the explicit real and complex Gamma pole sets for the real
blocks. A tensor block has real exponent equal to the sum of its two inputs,
and dualizing negates the real exponents. The two alternatives follow by
comparing the real spectral parameter to the negative sum of the smallest
left and largest right exponents.

`RealNormalizedGenerationInductionStatement` uses these alternatives to
propagate pointwise nonvanishing to pairs of nonempty ordered lists. It
accepts spaces of complex-valued functions on the spectral plane and
hypotheses for the inclusions between these spaces after multiplication by
the relevant denominators. Induction first treats a single right block.
An interchange hypothesis gives the single-left-block cases. Induction on
the total number of blocks then handles pairs of longer lists by selecting
a multiplier and a smaller pair whose member is nonzero at the specified
point. The smallest-exponent block is at the end of the left list in the
upper triangular convention. The largest-exponent right block is at the
beginning of the right list.

The denominator alternatives are the pointwise form of the pole
separations in H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009),
Propositions 12.3 and 12.4, pp. 85–86 of the author-posted version. The
multipliers in the induction are the ones obtained after normalizing the
inclusions in Proposition 14.3, pp. 104–107. The integral constructions that
supply the inclusions are premises of this result.

`RealNormalizedPointwiseGenerationInductionStatement` takes a complex subspace of scalar values at each spectral point for each pair of lists. The same three inclusions are imposed at each point with the same primal and reflected multipliers. Under the singleton and exchange hypotheses the scalar values cover the plane. To deduce this from the function-space induction, take the product of the scalar subspaces over the spectral plane. A scalar value at one point is represented by the function supported at that point. The hypotheses and conclusion of the function-space argument then give the pointwise result. This uses the denominator comparison of [Jacquet, *Archimedean Rankin–Selberg Integrals*, §14.3, pp. 107–108](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf#page=107).
