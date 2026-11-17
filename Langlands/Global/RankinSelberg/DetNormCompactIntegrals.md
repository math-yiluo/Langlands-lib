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

For the standard compact subgroup, `rectangularLIntegral_standardCompact_mul`
derives the padded symmetry from right standard compact invariance of the
original function. The published `pad_mem_standardCompact` puts the padded
element in the larger standard compact subgroup. The determinant-one
specialization and the rectangular change of variables then prove that
right multiplication by the original compact element preserves
`rectangularLIntegral`. The corollary
`rectangularLIntegral_standardCompact_mul_of_simpleRootGauge` extracts
measurability and compact invariance from `IsAdelicSimpleRootGauge`; it
does not use the gauge's Schwartz–Bruhat witness.

All ranks `t < r`, including the zero-row rectangle, are retained. The
construction uses only the published determinant, compactness, padding
and rectangular change-of-variables results. It applies to infinite
integrals as well and supplies no majorization, finiteness or Mellin
convergence.
