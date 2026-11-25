# Finite normalized row systems from powered maximal minors

This module contains the field-linear finiteness step used in the bracket
argument for torsion configurations. Here `K` is a field, `ι` is a set of
row labels, and `J` is a finite column index type. A row system is a function
`A : ι → J → K`. An ordered tuple of labels `p : J → ι` selects a square
matrix.

- `pivot A p` is the square matrix whose `k`-th row is `A (p k)`.
- `normalize A p` multiplies every row of `A` on the right by the inverse of
  `pivot A p`. Mathlib's matrix inverse is used, so this is only meaningful
  when the determinant is nonzero.
- `poweredMinor n A p` is `det (pivot A p) ^ n`.

## Results

`normalize_apply` is Cramer's rule. If the pivot determinant is nonzero, the
`j`-th coordinate of the normalized row `i` is the determinant of the matrix
obtained by replacing the `j`-th selected row with row `i`, divided by the
pivot determinant. The proof uses Mathlib's
`Matrix.det_smul_inv_vecMul_eq_cramer_transpose` and
`Matrix.cramer_transpose_apply`.

`exists_right_unit_of_normalize_eq` states the following. Suppose two row
systems `A` and `B` have nonzero determinants at the same pivot tuple and the
same normalized rows. Then one invertible matrix `G` satisfies
`A i ᵥ* G = B i` for every label `i`. Take `G = (pivot A p)⁻¹ * pivot B p`;
its inverse is `(pivot B p)⁻¹ * pivot A p`.

`exists_finset_of_projectively_equal_poweredMinors` is the finiteness
statement. Fix a positive exponent `n`, a pivot tuple `p` and a function
`c` from tuples to `K` with `c p ≠ 0`. A row system `A t` is given for every
index `t` of an arbitrary type `T`. Assume that for every `t` there is a
nonzero scalar `a` such that every powered minor of `A t` is `a` times the
corresponding value of `c`. In other words, all the powered minors are
projectively equal to `c`. The row label type must be finite. Then there is
a finite set `R` of indices such that every `A t` is carried to some
`A t'` with `t' ∈ R` by one invertible matrix acting on the right. The type
`T` may be empty, and then `R` is empty.

## Proof

Since `c p ≠ 0` and `a ≠ 0`, the pivot determinant of every `A t` is
nonzero. By Cramer's rule, the `n`-th power of each normalized coordinate
of `A t` is the quotient of two powered minors. The common scalar `a`
cancels, so this power equals `c (update p j i) / c p`, which is independent
of `t`. The polynomial `X ^ n - C v` is nonzero for positive `n`, so each
equation `x ^ n = v` has finitely many solutions in `K`. There are finitely
many row labels and columns, so the normalized row systems take values in a
finite product of finite sets. Choose a representative index for each value
that occurs. Two indices with the same normalized rows are related by an
invertible matrix, by the previous lemma.

## Use and provenance

This is an internal elementary lemma. It formalizes the linear algebra in the
context of the finiteness of labelled torsion configuration classes in the
fibres of a projective bracket map (`TorsionBracketMapStatement`). After trivializing the
`n`-th powers of the evaluation lines, the `n`-th powers of the maximal
minors of the joint evaluations give a point of projective space. On a fibre
over a geometric point, the normalized evaluation coefficients therefore have
only finitely many possible values. This is the calculation in step 5 of the
intended proof recorded in the Markdown of the published
`TorsionBracketMapStatement`: Cramer's rule expresses the evaluation
coefficients as ratios of brackets, and their `n`-th powers are ratios of
coordinates of the image point. The lemma is not taken from a literature
source and makes no geometric assertion. Converting sheaf-module evaluation data over a field into row
systems is not part of this module.
