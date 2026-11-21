# Multiplication of concordant functions by orbit values

`AreConcordant.mul_of_orbitValues` is a derived consequence of the Library's
concordance definition. The ordinary weight is constant on each regular conjugacy
class. The twisted weight has the same value as the ordinary weight along the twisted
orbit of each associated element.

The proof checks the descended orbit integrands on coset representatives. Their
weights are constant, so the constants factor out of the Bochner integrals. At a
regular non-norm the ordinary orbital integral remains zero after multiplication.
At an associated regular pair both integrals acquire the same factor, and the
original concordance identifies the two weighted integrals. The result holds for
the supplied compatible quotient measures and does not require the weights themselves
to have compact support.
