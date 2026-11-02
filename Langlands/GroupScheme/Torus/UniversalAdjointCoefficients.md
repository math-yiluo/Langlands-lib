# Finite coefficients of the universal split-torus adjoint action

This module is derived arbitrary-base infrastructure for the coefficient proof
of Milne, *Algebraic Groups* (2017), Theorem 12.12, printed pp.234–235
(PDF250–251). The source expands a diagonalizable representation in a group-like
basis, proves that the coefficients are eigenvectors, and recovers the original
vector by their sum. Here that method is implemented directly on the actual
dual-number identity kernels and the existing adjoint representation, whose
field-valued source is Milne 10.18–10.20, printed pp.191–192 (PDF207–208).
The module does not yet identify exponent vectors with the character lattice or
assert the internal-direct-sum theorem.

Let `R : CommRingCat` be arbitrary, let `I` be a finite type with decidable
equality in the same universe, and let `G` be an affine group scheme over
`Spec R`. Fix a homomorphism `i : splitTorus (Spec R) I ⟶ G`.
`universalAdjoint I G i` is the `R`-linear map that first extends a Lie vector
`X` from `R` to `R[I → ℤ]` and then applies `Ad(i(u))`, where `u` is the actual
universal torus point. The target uses the existing Lie module with scalars
restricted to `R`. Its addition is the actual point-group law and its scalar
action is epsilon scaling.

`universalAdjoint_map` proves that every `R`-algebra homomorphism out of
`R[I → ℤ]` evaluates this action to `Ad` of the corresponding evaluated point
on the constant extension of `X`. The proof uses adjoint naturality. Its private
constant-extension lemma follows by applying algebra maps to
identity-derivation coordinates.

`universalAdjoint_translatedEvaluation` applies this identity to the
translated-evaluation map associated with `t : I → Aˣ`, for every commutative
`R`-algebra `A`. The translated universal point is the product of the constant
point `t` and the coefficient extension of `u`. Since `Ad` is multiplicative,
the resulting action is the constant adjoint action of `i(t)` applied after
coefficient extension of the original universal action. These identities need
no local-finite-type assumption.

Assume in addition that `G.X.hom` is locally of finite type.
`universalAdjointCoefficients I G i` composes this linear action with the
existing finite coefficient map, obtaining an `R`-linear map
`Lie(G)(R) → ((I → ℤ) →₀ Lie(G)(R))`. Finite support uses finite generation
of the coordinates of the affine group, as supplied by the imported
coefficient API.

`universalAdjointCoefficients_weight` proves the exponent-weight equation for
each coefficient `p(X)(m)`: for every test algebra `A` and every `t : I → Aˣ`,
the actual `Ad(i(t))` sends the constant extension of `p(X)(m)` to
`↑(∏ j, t j ^ m j)` times that vector. The product and powers are taken in
`Aˣ`. The proof extracts the `m`-th coefficient of
`universalAdjoint_translatedEvaluation`. On one side, translated evaluation
scales that coefficient by the displayed unit value. On the other, coefficient
extraction commutes with the constant adjoint action and coefficient extension.
The resulting equation therefore quantifies all test algebras, including
nonreduced ones.

`universalAdjointCoefficients_of_monomial` says that if the universal action on
`X` is the monomial of exponent `m` times the constant extension of `X`, then its
coefficient family is `Finsupp.single m X`. It follows by extracting each
coefficient using the existing monomial formula.

Finally, `universalAdjointCoefficients_sum` proves that the finite sum of all
coefficients is `X`. The proof evaluates the finite monomial reconstruction at
the family of units all equal to one. This sends the universal torus point to
the identity, so its adjoint action is the identity. Each monomial evaluates to
one and constant extension evaluates back to the original vector. No field,
smoothness, or hypothesis on `i` beyond being a homomorphism is used.
