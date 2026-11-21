# Unnormalized induction can fail to preserve Hermitian representations

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, IV.2.1, paragraph after Remark 2, printed p. 97
(PDF p. 103). Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The definition of a t.d. group is in II.1.1, printed p. 30 (PDF p. 36).

`Langlands.Renard.CompactRepresentation.UnnormalizedInductionHermitianCounterexampleStatement`
says that some closed subgroup \(H\) of a Hausdorff locally compact totally
disconnected group \(G\), with compact left coset space \(H\backslash G\),
has a smooth complex Hermitian representation whose unnormalized induction
has no invariant nondegenerate Hermitian form. The declaration expresses
existence of a counterexample by negating the corresponding preservation
claim with both carriers in `Type`.

The form is conjugate-linear in its first argument and linear in its
second, with Hermitian symmetry, zero radical and invariance under the
given group action. This is the convention of
[`HermitianRepresentationStatements`](HermitianRepresentationStatements.md).
The target uses `Induction.compactInduced` on the actual coefficient
representation. Compactness of \(H\backslash G\) identifies this unnormalized
compact induction with smooth induction, as in Renard III.2.3 and
`Induction.compactInclusion_bijective_of_compactSpace`.
