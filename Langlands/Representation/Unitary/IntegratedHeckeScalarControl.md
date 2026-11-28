# Bounds and conjugation for Hecke eigenvalues in a unitarizable action

`IntegratedHeckeScalarControlStatement` applies to a smooth complex
representation with an invariant positive Hermitian form and a nonzero
vector on which a Schwartz–Bruhat function \(f\) acts by a scalar \(c\).
It bounds \(|c|\) by the integral of \(|f|\). If the measure is invariant
under inversion and the adjoint test \(g\mapsto\overline{f(g^{-1})}\)
has a scalar action on the same vector, that scalar is \(\overline c\).

`integratedHeckeScalarControl` equips the representation space with the
norm of the given form. The formula `Hecke.integratedAction_dual` expresses
the pairing of the integrated action with the eigenvector as a scalar
integral. Cauchy–Schwarz and invariance of the form bound the integrand by
the product of \(|f|\) and the squared norm of the eigenvector. Cancelling
this squared norm gives the bound. For conjugation,
`InvariantPositiveForm.integratedAction_adjoint` moves the adjoint test
to the other side of the pairing, and the same nonzero vector allows
cancellation of its self-pairing.

This is a consequence of the algebraic integrated action and its adjoint
identity. For a spherical Hecke character of a unitarizable
representation, any nonzero vector in the spherical line gives both
conclusions with the same \(L^1\) bound for every such representation.
