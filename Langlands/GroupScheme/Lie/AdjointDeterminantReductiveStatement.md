# Triviality of the actual reductive adjoint determinant

Author: Worker 107.

`Lie.ConnectedReductiveAdjointDeterminantStatement` asserts that the actual
rational character `Lie.adjointDeterminantCharacter G` is zero for every
connected reductive affine locally finite-type group scheme over every field
in universe `u`. The statement retains nonsplit groups and zero-dimensional
groups. It imposes no characteristic-zero or rational-point-surjectivity
assumption.

The accompanying lemmas prove the central part of the argument.
All-test centrality of a morphism `i : Z → G` makes its constant dual-number
points commute with every Lie-kernel point. Consequently their conjugation
differential is the identity. If `Z` is affine, the adjoint determinant
therefore restricts to the zero rational character on `Z`: its values are
one on every affine test algebra, and the chosen affine corepresentation
detects equality of the original group-scheme morphisms.

`connectedReductiveAdjointDeterminant_of_centralDerivedProduct` proves an
implication from the existing
`ReductiveCentralDerivedProductStatement` to the new statement. It uses
the supplied epimorphic product of a central torus and an actual derived
subgroup. The preceding central lemma annihilates the first factor;
`IsDerivedSubgroup.characterRestrict_eq_zero` annihilates the second.
The existing character-detection lemma for an epimorphic product then
annihilates the character on the whole group. The product theorem remains
an explicit premise of this implication; this module does not prove it
or the unconditional reductive statement.

This is the algebraic step of Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Corollary 3.6.2, printed pp.88–89, with the
all-algebra character in equation (3.13), p.90. The central-kernel argument
above describes the implemented proof; no analytic Haar comparison is
asserted here.

Source: `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`,
§3.6, Corollary 3.6.2 and equation (3.13). The October 2026 author errata
has no correction to these passages.
