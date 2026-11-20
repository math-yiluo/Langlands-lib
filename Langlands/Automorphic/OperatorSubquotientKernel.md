# Actual automorphic quotients from operator intertwiners

Given an actual operator-stable subspace of automorphic forms, let \(f\)
intertwine its action with a supplied representation of the whole operator
algebra. `ofIntertwinerKernel` keeps the actual form subspace as numerator
and uses the invariant kernel of \(f\) as denominator. The existing quotient
map and descent operations identify this quotient with the target of \(f\)
when \(f\) is surjective. Injectivity follows by taking a representative of a
kernel class. Surjectivity follows by taking the class of a preimage under
\(f\).

If the supplied target is irreducible, its equivalence with the quotient
transports irreducibility to the quotient. Restricting the same equivalence
along the finite translation homomorphism identifies the finite-adelic
actions. This lets a later proof transport local embeddings into the actual
automorphic quotient.

This is an internal packaging of the subquotient presentation for the
automorphic constituent in R. P. Langlands, *On the notion of an automorphic
representation* (1979), Proposition 2 and its converse proof, printed
pp. 204–206, PDF pp. 199–201 of Corvallis Part I
(`langlands-1979-notion-automorphic-representation`). It operates on a
supplied surjection from actual forms.
