# Polynomial pullback along the central zero-weight projection

This is an internal construction derived from the finite matrix weight
coefficients in `Rational.CharacterRestrictionFiniteIndex` and the existing
matrix-representation and polynomial-evaluation APIs. It supplies elementary
tools for the central-torus part of the Haboush reduction. No reductivity,
Steinberg-module or geometric-reductivity premise is used.

For a commutative ring `k`, a finite coordinate type `n : Type` and a square
matrix `P`, `MatrixRepresentation.linearPullback P F` substitutes
`∑ j, C (P i j) * X j` for coordinate `i` in `F`. The theorem
`eval₂_linearPullback` identifies its value after any ring homomorphism
`f : k →+* A` with the value of `F` at `P.map f *ᵥ x`.
`linearPullback_isHomogeneous` preserves each specified homogeneous degree,
including when substitution gives the zero polynomial.
`eval_linearPullback_of_fixed` preserves the value at any vector fixed by `P`.

The proof of the evaluation formula uses composition of substitutions and
evaluation of finite sums. The degree assertion applies the homogeneous
substitution theorem to linear coordinate forms. The fixed-vector assertion
specializes the evaluation formula to the identity homomorphism.
`IsInvariantPolynomial.linearPullback` then preserves the existing
all-test-scheme invariance predicate whenever the scalar-extended matrix `P`
commutes with every point matrix of the representation. This proof uses
associativity of matrix action and the supplied commutation identity.

The namespace `MatrixRepresentation.CentralZeroWeight` fixes a field
`k : Type u`, a group scheme `G` over `k`, a representation `ρ` with coordinates
`Fin N`, a finite type `I : Type u` with decidable equality, and a homomorphism
`j : splitTorus (Spec k) I ⟶ G`. Neither injectivity nor centrality of `j` is
needed for the definition `projection ρ I j`: it is the coefficient matrix
`weight ρ I j 0` of the trivial character in the universal torus matrix.

`projection_mul_self` follows from the published orthogonality of the weight
matrices. `projection_fixed` says that any vector fixed by `ρ.restrict j`
is fixed by this projection. Its proof specializes the supplied all-test
fixedness to the universal torus point over the group algebra `k[ℤ^I]` and
extracts the coefficient of exponent zero from the resulting vector equation.

`projection_mul_affine` proves `P_B * ρ(j(t)) = P_B` for every commutative
`k`-algebra `B : Type u` and every affine torus point `t`, with
`P_B = P.map (algebraMap k B)`. The proof expands the torus matrix as its finite
sum of character values times weight matrices. Multiplication by `P_B` kills
every nontrivial weight. The trivial character evaluates to one; if that weight
is outside the finite support, `P` is zero. `projection_mul_points` transports
the same identity to torus points over every test scheme. It chooses an affine
model of the split torus, applies the affine identity there, and pulls its
matrix coefficients back to the global sections of the test scheme.
The test scheme itself need not be affine.

`projection_commute` additionally assumes `IsCentral j` and `IsAffine G.X.left`
and specializes the published all-test commutation of central weight matrices.
Consequently `linearPullback_torus_invariant` makes every polynomial invariant
under the restricted torus action, without a centrality hypothesis.
`linearPullback_restrict_invariant` assumes centrality and affineness of `G`;
for any homomorphism `q : H ⟶ G`, it preserves invariance under `ρ.restrict q`.
Both conclusions use the existing invariance predicate on points and vectors
over every relative test scheme, including nonreduced tests.

These results construct the projection and polynomial pullback for a supplied
split torus. They do not produce an initial separating invariant polynomial,
prove that subgroup invariance implies full-group invariance, construct a
central-derived cover, or establish Haboush's theorem. The implemented scope
uses `Fin N` for the weight-projection part; the preliminary linear-pullback
lemmas allow any finite small coordinate type.
