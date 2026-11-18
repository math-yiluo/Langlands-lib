# Reduced norm of scalar hyperbolic scaling families

This internal helper proves the rank-one determinant formula for the canonical
reduced norm of a scalar matrix algebra, and applies it to the two polar line
projectors of a hyperbolic pair. All coefficient algebras are commutative
algebras over the ground field; they need not be reduced or fields.

The proof uses the scalar splitting chart and Mathlib's determinant lemma.
The two rank-one update factors have norms `t` and `t⁻¹`, and their cross
term vanishes by orthogonality of the polar projectors. Their product
therefore has reduced norm one. This extends the explicit scaling
construction in `QuadraticHyperbolicSplitTorus` and assumes neither
smoothness of the orthogonal group nor nondegeneracy of the full polar form.

For a finite hyperbolic family, the partial scaling sum is multiplied by
one further pair scaling at each insertion. The mixed products vanish by
the published orthogonality identities. Finite-set induction and
multiplicativity of reduced norm give norm one for the whole family.
`IsHyperbolicFamily.normOneScalingUnits` restricts the published scaling
homomorphism to the actual reduced-norm-one subgroup of matrix-algebra
units. Its underlying unit is the original family scaling unit.
The index type of the ambient nonzero finite-dimensional vector space
is in `Type`; the ground field and coefficient algebras have arbitrary
universe `u`, and the finite family index lies in `Type u`.

This is an internal algebraic consequence of the published scalar involution,
hyperbolic-pair projectors and family scaling constructions, the canonical
reduced norm evaluated in a splitting chart, and Mathlib's determinant
lemma. It introduces no new literature translation and makes no
classification or central-isogeny claim.
