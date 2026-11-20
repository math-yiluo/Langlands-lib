# Poincaré–Birkhoff–Witt coordinates for the two-block grading

This two-block decomposition is for the parabolic projection in
Harish-Chandra (1968), Chapter I, §6, printed pp. 19–20 (PDF pp. 29–30).
The matrix units are ordered by the adjoint weights of the block
grading element, with the upper radical first, then the Levi and the
lower radical. Weight-zero ordered monomials have equal numbers of
upper and lower radical letters.

`blockPBWBasis` applies the library's Poincaré–Birkhoff–Witt theorem to
that order. Commuting with the grading element forces all the nonzero
basis coefficients to have weight zero. A weight-zero monomial
with no upper radical letters also has no lower radical letters, so
it comes from the enveloping algebra of the block diagonal Lie
subalgebra. A monomial with an upper radical letter starts with one,
so it belongs to the span of products of an upper radical generator
on the left and an arbitrary enveloping element on the right.

`mem_levi_sup_upperRadicalRightSpan_of_commute` gives this decomposition
for every element commuting with the grading element. It applies in
particular to the central operators used in the constant-term
argument.
