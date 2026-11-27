# Bruhat expansion of a truncation kernel series

For one standard parabolic cutoff kernel and a fixed testing parabolic, `constantTerm_cutoffSeries_bruhat` gives the sum over minimum Weyl representatives. In each cell it identifies the outer rational cosets and the integral over the smaller target radical, with the normalized intertwining measure. The integrand is evaluated at `w⁻¹ v δ x`, using the constant term along the smaller source parabolic and the cutoff of the original summand. The theorem also provides integrability in each such fiber and summability over its outer rational cosets.

The cutoff kernel is measurable and invariant under the source radical and the source rational parabolic. Its absolute coset sum is uniformly bounded on the testing radical orbit. The measurable series unfolding and `GeometricLemmaUnfoldingStatement` give the smaller radical integral. Equality of the actual standard subgroup maps transports its quotient, and `constantTerm_cutoffKernel_of_subset` pulls out the cutoff and collapses the nested radical average.

The calculation follows the architecture of Bernstein–Lapid (2024), §6.10, equation (6.17), pp. 208–209, applied to the measurable kernel from Arthur's truncation formula.
