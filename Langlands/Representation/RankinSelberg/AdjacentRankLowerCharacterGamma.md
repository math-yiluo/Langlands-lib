# The arbitrary-character lower adjacent gamma product

This internal module removes the large-real-twist restriction for the actual
lower adjacent-rank induction, conditional on the explicitly supplied complete
unramified gamma transport proposition. It does not supply a proof of that
transport proposition or claim the closed parent target.

The proof chooses fixed complete L-polynomial certificates and fixed gamma
certificates for the two blocks. Their constant terms are one by the shared
`IsPadicSymmetricLPolynomial.coeff_zero` lemma in
[PadicPairLPolynomialNormalization](PadicPairLPolynomialNormalization.md).
Taking the maximum of their real bounds puts
the certified finite clearing and the actual gamma equations on the same real
ray. The canonical gamma construction supplies a complete ambient certificate
at zero. Its nonzero rational witness chooses one original model vector and one
test vector. The actual corank continuation theorem continues the product
equation to this pair at zero, including the translated dual integral.
Rational-continuation uniqueness identifies both functions with those in the
ambient certificate. Since the original witness is nonzero, scalar gamma
uniqueness identifies the ambient factor with the product of the two fixed
factors. The resulting equality rewrites the whole ambient certificate.

The actual zero-deformation equivalence then transports this complete
certificate to the ordered lower induction, and complete-certificate
commutation puts the test representation first. All original carriers,
independent universes, measure quantifiers, functional quantifiers, and nonzero
witness clauses are retained through these existing complete relations.
No irreducibility is assumed. This is a derived composition of the existing
analytic, deformation, gamma-construction, and transport results.
