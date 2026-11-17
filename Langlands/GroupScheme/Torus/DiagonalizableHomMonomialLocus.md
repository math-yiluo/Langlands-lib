# Idempotent restriction loci of actual diagonalizable homomorphisms

This internal construction applies the grouplike monomial-locus argument
to actual homomorphisms between affine diagonalizable group schemes over
an arbitrary commutative ring. Its provenance is derived from the
Library's explicit character point model, natural-unit description of
homomorphism coordinates, and the grouplike monomial-locus construction.

For `f : D_R(Γ) ⟶ D_R(Λ)`, `homCharacterFamily f` is the universal
character-coordinate family with values in the units of `R[Γ]`.
It is obtained by evaluating `f` at the universal point and transporting
the resulting global functions through the affine section isomorphism.
Every coordinate is grouplike, by the existing natural-unit theorem.

`points_eq_of_monomial_specialization` states that if the family becomes
the monomials prescribed by `p : Λ →+ Γ` after the coefficient map
to global functions on a test scheme, then `f` and character restriction
along `p` agree on that test's entire point group.
The proof evaluates the specialized group-algebra equality at each
character point. The existing natural-unit value formula identifies
the evaluation with the corresponding coordinate of `f`.

If `Λ` is finitely generated, `exists_idempotent_restriction_locus`
shows that any coefficient specialization to a domain supplies `p`
and an idempotent `e` of `R` whose image at that specialization is one.
For every test scheme where the image of `e` in global functions is
one, `f` agrees with restriction along `p` on all points.
This retains torsion in both character groups and permits zero
divisors and nilpotents in `R`.

The resulting all-test certificate is intended for constructing local
presentations. This module does not yet package those loci as an open
cover or assert surjectivity of the extracted character map for closed
subgroup inclusions.
