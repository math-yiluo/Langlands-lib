# Rational characters of GL and its block Levi subgroups

This file proves `Langlands.GroupScheme.GeneralLinearCharactersStatement`.
It covers every field and every rank, with the separate trivial-character
case in rank zero and scalar split-component maximality in positive rank.
The block determinants form the specified integral basis for every positive
block shape.

The rational-character and split-component conventions are those of Renard,
*Représentations des groupes réductifs p-adiques* (2026), V.2.1–2, printed
pp.104–105, V.3.6, printed p.111, and Waldspurger,
*La formule de Plancherel pour les groupes p-adiques d'après Harish-Chandra*
(2003), I.1, printed pp.238–239. The GL and block calculations here are
derived examples of those constructions.

For a character of GL, restriction to one coordinate cocharacter gives an
integer by the published classification of multiplicative-group
endomorphisms. Permutation conjugacy identifies the diagonal restrictions.
Diagonal scaling and the transvection addition law kill all transvections
over an enlarged generic field containing an element other than zero and
one. The matrix-generation theorem gives the determinant-power formula in
that field. Injectivity from the GL coordinate ring and specialization of
the universal matrix prove the formula on all test algebras; affine values
detect equality of scheme morphisms. A coordinate cocharacter distinguishes
the integer powers. Empty matrices form the trivial group.

The determinant of a scalar matrix is the scalar raised to the rank, which
proves the scalar restriction formula. For positive rank, central matrices
over every test ring are exactly scalar matrices. Extracting their scalar
units gives a natural factor to the multiplicative group. For any central
subtorus containing the scalar torus, the factorization maps are inverse by
monicity. This proves maximality.

For a block Levi, its points are naturally tuples of invertible blocks.
Scheme projections and inclusions give an ordered product decomposition of
each point. Applying the GL calculation to each block expresses any
character as a sum of block determinant powers. The first coordinate
cocharacter of each block extracts its exponent, proving independence.
Transporting the usual basis of integer tuples gives exactly the required
block determinant basis.

The final theorem assembles these proofs from
`GeneralLinearCharacterAdapters` and `BlockCharacterProof`. The detailed
generic-field, matrix-factorization, affine-evaluation, and central-scalar
constructions are described in their paired Markdown files. No general
connected-reductive structure statement is assumed or proved here.
