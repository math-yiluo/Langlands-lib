# Coefficient bounds on a finite lattice of actual compressed operators

Author: Worker 19.

`Langlands.CompressedLatticeCoefficientBoundStatement` is a derived internal
proposition for a complex admissible representation of a topological group.
The group, vector-space and finite-index universes are independent. An empty
index type is allowed.

It fixes a compact open subgroup `K` and actual subgroups `N`, `M`, `Nbar`.
The displayed factorization of every `k ∈ K` into lower, middle and upper
factors is a hypothesis. A homomorphism from the multiplicative form of
`I → ℕ` supplies the actual lattice elements. Three further hypotheses give
the upper, lower and middle conjugation inclusions used by the published
`Jacquet.compressedAction_mul_of_factor`. No geometric existence result is
asserted here.

For each generator `τ (Pi.single i 1)`, every eigenvalue of its actual compact
compressed action must have norm less than the supplied positive number
`s i`. The conclusion provides positive `a i < s i` and, for each `K`-fixed
vector and `K`-fixed dual functional, a positive constant `C` such that the
coefficient on every lattice element is bounded by `C * ∏ i, (a i)^(n i)`.
There is no polynomial factor.

The internal derivation uses finite dimension of `K`-fixed vectors, the finite
spectrum of each generator, the published endomorphism power bound and
submultiplicativity. Compression is multiplicative by the explicit
factorization hypotheses; the finite coordinate decomposition of `n` gives
the product bound. A fixed dual functional sees a vector through its compact
average, so evaluation of compressed operators gives the original coefficient.

This isolates the spectral-to-coefficient step. A consumer must still prove
the factorization and conjugation hypotheses, supply the generator spectral
bounds from actual normalized Jacquet exponents, cover the group modulo its
full center, compare Haar volumes and prove integrability. This statement
adds no premise to the final rational strict Jacquet criterion and proves no
geometric or integration assertion by itself.
