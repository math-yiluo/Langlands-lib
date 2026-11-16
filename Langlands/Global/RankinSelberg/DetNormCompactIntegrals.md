# Compact subgroups and the rectangular determinant factor

This internal helper works with every number field `F : Type u` and the
actual adelic general linear group-scheme points. `detNormHom` retains the
positive real units codomain of the normalized determinant character.
It composes the published continuous determinant norm on adelic matrices
with the published adelic-point homeomorphism. Its real value is exactly
the existing `detNorm`.

`detNorm_eq_one_of_mem_compactSubgroup` applies the Library's
`continuousMonoidHom_eq_one_on_compactSubgroup` to this character. The
reused theorem proves that a continuous positive real character is one
on a compact subgroup: its maximum bounds all squares, and the bound on
inverses gives equality. The specialization
`detNorm_eq_one_of_mem_standardCompact` instead applies the same theorem
directly on adelic matrices, using the Library's compactness of the
standard orthogonal, unitary and integral subgroup.

Under compactness of the additive adelic quotient, the exact
`rectangularRightIntegral_eq` formula then has scalar factor one at any
point of a compact subgroup. Likewise, if right multiplication by the
padded compact element preserves an input function, it preserves its
rectangular lower integral. The implemented proofs substitute determinant
norm one in the existing formulas, without cancelling an integral that
could be infinite.

The invariance theorem retains measurable input and the explicit padded
right-symmetry hypothesis. This helper does not assert that padding maps
one compact subgroup into another. All ranks `t < r`, including the
zero-row rectangle, are retained. The construction uses only the
published determinant, compactness and rectangular change-of-variables
results; it supplies no majorization, integrability or Mellin convergence.
