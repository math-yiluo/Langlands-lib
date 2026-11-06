# Coefficients of diagonal group-like elements

This internal algebraic helper is part of the proof of the open isomorphism
locus for diagonalizable group schemes. It works over an arbitrary commutative
ring, including rings with nilpotents and nontrivial idempotents. The degree
monoid is any additive commutative monoid.

For a group-like element `x` of `AddMonoidAlgebra R M`, the implemented proof
contracts its comultiplication in degree `m`, using
`DiagonalCoalgebraImage.contract_comul`. Comparing this with
`comul x = x ⊗ x` gives
`x.coeff m • x = single m (x.coeff m)`. Extracting coefficients proves
idempotence and pairwise orthogonality. The counit is the finite sum of the
coefficients, so that sum is one.

`coefficientPartition` constructs the corresponding finitely supported family,
with its idempotence, orthogonality, and sum-one proofs as certificates.

Multiplying the contracted identity by an inverse shows that a unit coefficient
forces `x = single m 1`. The same argument after a ring scalar extension proves
the corresponding assertion whenever the image of the coefficient is a unit;
the principal-localization result is its immediate specialization.

These lemmas are derived directly from the standard monoid-algebra coalgebra
structure in Mathlib. They are internal prerequisites rather than an assertion
of geometric representability or an open isomorphism locus.
