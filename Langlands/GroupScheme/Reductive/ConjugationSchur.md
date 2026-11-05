# Scalar values in irreducible conjugation representations

This internal construction isolates the elementary Schur-lemma step of the
positive-characteristic endomorphism-map argument. It works over an algebraically
closed field `k : Type u` of arbitrary characteristic. The supplied `σ` is an
actual group-scheme representation. Its rational-point representation is
explicitly assumed irreducible; this module proves no existence of such a `σ`.

`MatrixLinear.eval_map` proves that evaluation at a scalar-extended vector is
entrywise scalar extension of the base-field evaluation. The proof expands the
finite sum and applies preservation of sums and products by a ring homomorphism.

`MatrixRepresentation.rationalIntertwiningEndomorphism` constructs the
endomorphism of `σ.rationalRepresentation` given by a supplied matrix commuting
with every rational matrix of `σ`. This construction requires no irreducibility
or algebraic closedness.
`eq_smul_one_of_commutes` applies Mathlib's finite-dimensional Schur
lemma over an algebraically closed field makes this endomorphism a scalar.
Injectivity of the matrix-to-linear-map correspondence gives the scalar-identity
formula for the original matrix.

For an actual `ConjugationLinearMap φ`, `eval_fixed_commutes` specializes its
unchanged all-test equivariance equation to rational points and the image of
a supplied all-test fixed vector. It uses the canonical isomorphism
`Γ(Spec k, O) ≅ k`, then multiplies the conjugation equation by the invertible
matrix to obtain commutation.
`exists_nonzero_scalar_of_eval_ne_zero` applies the matrix form of Schur's
lemma. A nonzero matrix image forces the resulting scalar to be nonzero.

These are derived consequences of the existing coefficient definitions and
Mathlib's Schur theorem. They do not construct Steinberg modules, prove their
irreducibility, or embed regular functions in their endomorphisms. In particular,
they do not prove `SimplyConnectedPositiveCharConjugationMapStatement` or
Haboush's theorem. Those existence and nonvanishing obligations remain.
