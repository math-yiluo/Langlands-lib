# Compact-finite complex Godement sections

`ComplexGodementKFiniteStatement` applies to a smooth test supported
compactly inside the full-row-rank locus. When the right translates of
that test under the larger unitary group span a finite-dimensional space,
its Godement integral is a compact-finite vector in the larger standard
module. The smaller input can be any smooth standard module vector.

Right translation of the section moves the translating matrix to the
right of the rectangular test argument and contributes its determinant
weight. The proof establishes linearity of the Godement integral on
continuous tests with full-row-rank compact support. The right test
translations lie in this space because multiplication by an invertible
matrix is a homeomorphism preserving row rank. The span of the larger
unitary orbit of the section is contained in the image of the
finite-dimensional test orbit span under the linear map. The smooth
standard module membership follows from `complexGodementCompactSmooth`.

This derives compact finiteness of such sections from the right action
used in Jacquet's proof of Proposition 7.1(vi). [Jacquet, *Archimedean Rankin–Selberg integrals*, §7.1, pp. 43 and 46–47](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
