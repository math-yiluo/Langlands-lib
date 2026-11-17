# A Schwartz majorant for compact translates of a coordinate row

This internal helper restricts a Schwartz–Bruhat function Φ on adelic
rows of length n to rows supported in a fixed coordinate i, after right
multiplication by any matrix in a compact subset Q of the actual adelic
general linear group. It constructs a Schwartz–Bruhat function φ on a
one-dimensional adelic row whose norm bounds all of these values.

`exists_compact_row_majorant` first gives the corresponding result on the
whole row space: one Schwartz–Bruhat function bounds every right translate
by Q. It applies uniform compact-translate domination at every exponent
and the general majorant construction to the family indexed by all rows
and all members of Q.

`coordinateRow` places an adele in coordinate i and zero in every other
coordinate. `singleRow` represents the same adele as a one-dimensional
row. The archimedean norm of the latter is at most that of the former:
evaluation at i recovers the same archimedean coordinates.

The proof uses the published compact-translate domination theorem
`EqualAnalytic.exists_uniform_dominated`. Applied at exponent zero it
provides one finite denominator valid for every nonzero value on Q.
Applied at every natural exponent it provides uniform rapid decay in
the original row norm, which controls the one-dimensional row norm.
The general construction `SchwartzMajorant.exists_schwartzBruhat_majorant`
then produces φ from this indexed family, using the common finite cutoff
and a rapidly decreasing archimedean majorant.

`lastRow_mul` identifies the last row of a product with the product of the
last row and the second matrix. `lastRow_diagonalPoint` computes the last
row of the actual group-scheme point associated to a diagonal matrix.
The compact set of group-scheme points maps continuously to a compact
set of adelic matrices. Applying the coordinate-row result to that image
gives `exists_compact_lastRow_majorant`. Its diagonal specialization,
`exists_compact_diagonal_lastRow_majorant`, bounds the last-row factor
uniformly over the compact translates using only the last diagonal idele.

This is derived analytic infrastructure, not a translation of a source
theorem. It provides a pointwise bound only. It does not assert
integrability on a Whittaker quotient or prove the full-rank gauge
Mellin proposition.
