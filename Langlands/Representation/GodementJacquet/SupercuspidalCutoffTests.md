# Actual determinant-unit cutoff matrix tests

This derived construction turns an actual smooth-dual coefficient of a
positive-rank supercuspidal general linear representation into a full-matrix
Schwartz–Bruhat function. The field and representation carrier retain their
independent universes. The coefficient is unchanged on determinant norm one
and is zero on every other determinant shell and on singular matrices.
The construction is complex linear in the representation vector.

The determinant-unit subgroup is open in GL, and GL has its actual open
embedding into the matrix space. Their composite is an open embedding.
A compact test on the subgroup is transported to its open image and extended
by zero using the published Schwartz–Bruhat extension map. Its topological
support lies in the subgroup image. Local constancy of the restricted
coefficient follows from smoothness of the representation, and its compact
support is the preceding Harish-Chandra specialization in
`SupercuspidalCoefficientTests`.

Godement and Jacquet, *Zeta Functions of Simple Algebras* (1972),
Proposition 5.5(2), printed page 62 (one-based PDF page 72), motivates the
determinant-unit coefficient cutoff. The registered source
`godement-jacquet-1972-zeta-simple-algebras` is retained at
`/home/taskhub/central-library/Godement-Jacquet--Zeta functions of simple algebras (book)--1972.pdf`,
SHA256 `86a8900900504adeb5757a04b5bb8a8754e6ef00b0fff49754096d371f59d568`.
The present construction is for arbitrary smooth algebraic-dual coefficients;
it does not yet establish the singular vanishing of their Fourier transforms,
a nonzero integral operator, or the functional equation.
