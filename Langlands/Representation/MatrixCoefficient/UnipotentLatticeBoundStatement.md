# Uniform-degree coefficient bounds for unipotent lattice actions

Author: Worker 836, Task 5326.

`Langlands.UnipotentLatticeCoefficientBoundStatement.{u}` is an auxiliary
Prop-valued statement for the polynomial-growth step in the proof of
`Langlands.HarishChandraSchwartz.RationalXiUpperBoundStatement`. This module
states the auxiliary assertion; it does not prove it.

For natural numbers `d` and `r`, let `ρ` be a complex representation of the
integer lattice `ℤ^d` on any complex vector space `V : Type u`. For each
coordinate generator `e_i`, assume `(ρ(e_i) - 1)^r = 0` as an endomorphism
of the whole space. Then for every vector `v` and algebraic linear
functional `ell`, there is a nonnegative real number `C` such that

`‖ell (ρ(n) v)‖ ≤ C (1 + ∑ i, |n_i|)^(d*r)`

for every integer tuple `n`. The degree `d*r` depends only on the lattice
rank and the supplied common nilpotence exponent. In particular, it is
independent of the vector, functional and integer tuple. The multiplicative
type synonym on `Fin d → ℤ` adapts the additive lattice to the existing
representation API; negative coordinates are included.

The space `V` need not be finite-dimensional or carry a topology or norm.
Only the scalar-valued coefficient has a norm. The statement also includes
`d = 0`, `r = 0` and the zero vector space; it assumes neither a nonzero
coefficient nor a positive nilpotence exponent.

This is a derived algebraic auxiliary statement, rather than a transcription
of a separately numbered result in the literature. Its intended route is
to apply the published finite binomial expansion
`Langlands.integerUnipotentBinomial` to each generator, bound each scalar
binomial polynomial, and expand along the finitely many coordinates. The
operator formula is in
`Langlands/LinearAlgebra/UnipotentBinomialProof.lean`. The explicit degree
bound here is deliberately allowed to exceed the optimal degree. No
exponential-polynomial expansion, eigenbasis, finite-dimensionality
assumption, or previously assumed growth estimate is part of this
auxiliary statement.

For the intended application, the lattice acts through the center of a
standard Levi on a normalized Jacquet module. Establishing that action,
its unipotence, the decomposition of a chamber into lattice cosets and the
comparison with the actual matrix height remain separate obligations.
