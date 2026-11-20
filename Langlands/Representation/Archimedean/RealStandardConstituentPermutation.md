# Constituents of reordered real standard modules

`realStandardOperators` packages the action of `O(n)` and the right-derivative
actions along real matrices. For an adjacent exchange of blocks, shift the
complex exponent of the same block in each order. There are infinitely many
purely imaginary shifts for which the two exchanged exponents have distinct
imaginary parts. Mœglin linkage forces the corresponding exponents to have
equal imaginary parts. The real parts retain their order along these shifts,
so the Library's unlinked swap and surjectivity results give an intertwining
isomorphism at each chosen parameter, inverting it as needed.

The two compact equivalences conjugate these isomorphisms to the fixed base
spaces. The real infinitesimal generators on each space vary affinely while
the compact action is fixed. Compact affine specialization then transfers the
irreducible quotient of a stable subspace across the exchange at zero. The
induction on `List.Perm` carries the same constituent across any permutation.

This implements the occurrence comparison for the Library's real standard
modules by specialization. The normalized-product comparison is motivated by
Badulescu–Renard (2010), Remark 2.3 and Proposition 2.4, pp. 1123–1124 (PDF
pp. 10–11). The linkage test and adjacent intertwining input use Mœglin,
*Representations of GL(n) over the real field* (1997), §8, p. 163, and §10,
Theorem 10b and its proof, pp. 164–165 (PDF pp. 172–174 in the registered
Bailey–Knapp volume).
