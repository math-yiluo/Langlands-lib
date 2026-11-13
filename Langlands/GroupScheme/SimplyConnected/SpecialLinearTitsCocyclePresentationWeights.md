# Diagonal weights of the finite Galois special-linear presentation

This internal specialization attaches the diagonal characters to the actual
finite Galois `Presentation d e`. It combines the presentation construction of
Worker 243 with the finite-stage diagonal weights, using the original maximal
split torus, root restrictions and numbering of the supplied Tits index.
It introduces no new literature assertion.

`Presentation.diagonalWeights p i` is `stageDiagonalWeight` for `p.stage`,
`p.torusIso` and `p.coordinate`. These are characters of the original maximal
split torus over the ground field, descended through the canonical character
base-change equivalence.

`Presentation.numbering_index` identifies the original index corresponding to
a numbered stage simple root. The proof applies the injective original
numbering `e` to the corresponding equality of simple vertices. Both images
are `i` by the defining composite for `p.numbering`; taking subtype values
then gives the index equality.

`Presentation.rootRestriction_diagonalWeights` gives precisely the original
simple-root restriction as the difference of adjacent diagonal characters.
It uses the algebra structure on the separable closure induced by
`p.embedding`, the presentation's tower equality and full weight-map
comparison, and the preceding numbering identity. The general numbered
finite-stage root-restriction lemma then applies directly.

`Presentation.diagonal` gives the diagonal matrix formula for `p.localIso`
on every original relative test scheme, cover point, and point of the original
maximal split torus. The presentation's inclusion square and its explicit
local-isomorphism composite supply the hypotheses of
`diagonal_stageDiagonalWeight`.

The fields, characteristics, universe and rank are unrestricted, including
ranks zero and one. These lemmas establish the diagonal and root-restriction
clauses for a supplied presentation; they do not assert the Galois discrepancy
matrix formula. The reused presentation and its prerequisites retain their
original provenance.
