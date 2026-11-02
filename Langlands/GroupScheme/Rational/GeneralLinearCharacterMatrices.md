# Matrix algebra for GL characters

This internal construction supports the rational-character classification for
GL in Renard, *Représentations des groupes réductifs p-adiques* (2026), V.2.2,
printed p.105, and Waldspurger, *La formule de Plancherel pour les groupes
p-adiques d'après Harish-Chandra* (2003), I.1, printed pp.238–239. The abstract
matrix result here is a derived prerequisite, not a statement quoted there.

`diagonalMatrixUnits` embeds a tuple of units as an invertible diagonal matrix.
`coordinateDiagonalUnits` changes only a specified diagonal entry.
`characterTransvectionUnit` equips a transvection with its explicit inverse.

For a homomorphism from GL over a field to any commutative group, permutation
conjugacy identifies its restrictions to the individual diagonal entries.
Multiplying those entries reduces its value on every invertible diagonal matrix
to its value on a single entry equal to the determinant.

If the field has an element `s` different from zero and one, conjugation by a
diagonal matrix scales a transvection parameter by `s`. With
`b = c / (s - 1)`, the identity `b + c = s b` and the transvection addition
law show that the homomorphism kills the transvection with parameter `c`.
Mathlib's diagonal/transvection induction then proves determinant factorization.
The field-size hypothesis is retained; this is not a claim about arbitrary
abstract characters over the two-element field.

The diagonal and permutation parts of this proof adapt the published Library
proof in `Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity`;
the scaling argument replaces its positivity argument and applies to every
commutative target group.
