# Finite equations for diagonal bialgebra surjectivity

For a bialgebra map `φ : B → R[M]`, `coefficientIdeal φ m` is the ideal of
coefficients in degree `m` occurring in its algebra image. The monoid `M` is
commutative. After arbitrary commutative scalar extension `R → A`, the map
`A ⊗ B → A[M]` is surjective if and only if each of these coefficient ideals
extends to the unit ideal. No field or flatness assumption is needed.

The forward implication extracts coefficients from preimages of monomials.
For the reverse implication, the published homogeneous-coefficient extraction
lemma places each coefficient times its monomial in the algebra image. Taking
linear combinations in each degree then gives the monomial with coefficient
one. All monomials span the target algebra.

If `M` is finite and `B` is of finite type over `R`, every coefficient ideal
is finitely generated. Indeed the algebra image is a finite-type subalgebra of
the finite `R`-algebra `R[M]`; it is integral and hence finite as an `R`-module.
A coefficient ideal is the range of a linear map from this finite module.
`surjectivityIdeal φ` is the finite product of all degree coefficient ideals.
It is finitely generated, and scalar extension is surjective exactly when
this product becomes the unit ideal. These statements are derived internal
algebraic infrastructure for a quasi-compact open closed-embedding locus.
