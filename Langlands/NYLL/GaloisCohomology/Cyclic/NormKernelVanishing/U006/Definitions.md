# NYLL M004.006: finite-cyclic H¹ and Tate H⁻¹ comparison

The paired Lean file extracts
`Langlands.NYLL.CyclicCohomology.finiteCyclicH1IsoTateHMinusOne`
from Naganori Yamaguchi's ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`,
M004.006, lines 104–119 (definition at line 109). The complete section
context is at lines 26–32. The source file SHA-256 is
`06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

The complete telescope is an implicit `G : Type`, implicit `[Group G]`
and `[Fintype G]`, then explicit `A : Rep.{0} ℤ G`, `g : G`, and
`hg : ∀ x, x ∈ Subgroup.zpowers g`. The result is the actual categorical
isomorphism
`groupCohomology.H1 A ≅ tateCohomology A (-1)`.
Both the group and the representation carrier retain the source's universe
zero. The source's unused `universe u` does not occur in this declaration.
No commutativity, cyclicity or cohomology-vanishing hypothesis is added.
This remains noncomputable isomorphism data.

The construction first obtains a local `IsCyclic G` from the specified
generator, then the local `CommGroup G` supplied by
`IsCyclic.commGroup`. Mathlib's
`Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 ⟨0, rfl⟩`
identifies degree-one group cohomology with the homology of
`Rep.FiniteCyclicGroup.subCompNormHom A g`.
Composing with the inverse of the published
`Langlands.NYLL.TateCohomology.isoFiniteCyclicNegOne A g hg`
gives the displayed isomorphism to Tate cohomology. The latter is imported
from
`Langlands.NYLL.GaloisCohomology.Cyclic.TateComparison.FiniteCyclic.Definitions`;
it is the existing M003.003 construction.

The source helper M004.001, `CyclicCohomology.isCyclic_of_generator`
(lines 34–45), is discharged here by Mathlib's
`isCyclic_iff_exists_zpowers_eq_top` and `Subgroup.eq_top_iff'`.
Their composition turns `hg` into `Subgroup.zpowers g = ⊤` and then
`IsCyclic G`, with exactly the source helper's telescope. This local
replacement was checked directly in the approved environment.
No standalone copy of that helper is introduced. The supplied
`CommGroup G` instance is local to the construction.

Worker 120's modifications are extraction of M004.006, prefixing the
namespace by `Langlands.NYLL`, using the published M003.003 import and
qualified name, replacing M004.001 by the Mathlib composition above, and
omitting unrelated declarations, the unused universe declaration and the
unused invariants and closed-subgroup imports. The isomorphism composition
and the finite-cyclic calculation retain the source construction. A
private probe reproduces the complete original module with only its
namespace and M003 import/name adapted: equality of the entire unapplied
original and adapted M004.006 constants is proved by `rfl`. A separate
assignment checks the complete universe-zero telescope. The focused
module and this probe compile in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, establishing that M004.002–005
are unnecessary imports for this unit.

This contribution supplies the comparison data. The elementwise
norm-kernel consequence M004.007 and the extension predicates M004.002–005
remain separate units. It asserts no host class-formation, reciprocity,
cup, transfer or Tate result.

The original copyright, Apache-2.0 release and author header are preserved.
The retained license and notice are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
