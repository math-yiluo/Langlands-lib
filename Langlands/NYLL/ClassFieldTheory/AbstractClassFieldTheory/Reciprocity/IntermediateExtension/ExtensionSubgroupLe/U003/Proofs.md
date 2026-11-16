# NYLL M076.003: `extensionSubgroup_le_intermediateSubgroup`

## Exact target

The theorem
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_le_intermediateSubgroup`
has the telescope `{G : Type u_1} [Group G] [TopologicalSpace G]
{K : ClosedSubgroup G} (L : FiniteGaloisSubextension K)
(S : Subgroup L.extensionQuotient)` and type
`extensionSubgroup_le_intermediateSubgroupStatement L S`. That is the published target
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_le_intermediateSubgroupStatement`
of module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.ExtensionSubgroupLe.Statements`.
It says that for a finite Galois extension `L | K` and any subgroup `S` of
`G(L/K) = G_K ⧸ G_L`, the subgroup
`extensionSubgroup K L.field L.below` (that is, `G_L` viewed inside `G_K`) is
contained in `L.intermediateSubgroup S`, the inverse image of `S` in `G_K`.
There is no `[IsTopologicalGroup G]` hypothesis.

## Implemented proof

1. `intro x hx` takes `x : K.toSubgroup` with `hx : x ∈ G_L`.
2. `change L.extensionQuotientMk x ∈ S`: by definition,
   `L.intermediateSubgroup S = S.comap L.extensionQuotientMk` (M076.001), so
   membership in it is definitionally membership of the image in `S`.
3. The published theorem
   `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.extensionQuotientMk_eq_one_iff`
   (M040.013) has type `extensionQuotientMk_eq_one_iffStatement L x`. A
   `show` unfolds it to
   `L.extensionQuotientMk x = 1 ↔ x ∈ extensionSubgroup K L.field L.below`.
   Its reverse direction applied to `hx` gives `L.extensionQuotientMk x = 1`.
4. Rewriting with this equation leaves `1 ∈ S`, closed by `S.one_mem`.

## Dependencies

- Imported published modules:
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.ExtensionSubgroupLe.Statements`
  (the target and, through its imports, `intermediateSubgroup`,
  `extensionQuotientMk` and `extensionSubgroup`) and
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.U013.Proofs`
  (`extensionQuotientMk_eq_one_iff`, M040.013).
- The source proof also uses M076.002 `mem_intermediateSubgroup_iff`, which
  is not in the Library at this file's base. Its source proof is `Iff.rfl`,
  so the `change` in step 2 replaces it. No helper declaration is added.
- Mathlib: `Subgroup.one_mem`.
- Axioms reported by the Lean service: `propext`, `Classical.choice` and
  `Quot.sound` only.

## Source and modifications

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean`
(file SHA-256 `f031b91cd496accfb520a0665cbb59f5f8a4ac0f567ee2c5a5dffc408ef05b44`),
lines 57–67 (M076.003, `omit [IsTopologicalGroup G] in` at line 57). The
readable pinned source is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Its registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement`
(`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

Modifications by Worker 756, 16 November 2026:

- The namespace is prefixed with `Langlands.NYLL`. The source imports are
  replaced by the two published modules above, and the unused
  `open KummerTheory` is dropped.
- The theorem's type is the published `Statement` applied to the source
  parameters. The section variables omit `[IsTopologicalGroup G]` instead of
  using the source's `omit … in`, matching the statement's telescope.
- `apply (L.mem_intermediateSubgroup_iff S x).2` (unpublished M076.002) is
  replaced by the definitional `change` described above.
- The use of `L.extensionQuotientMk_eq_one_iff x` goes through a `show`,
  because the published theorem is stated through its `Statement` wrapper.
  The remaining proof steps are the source's.

The original copyright and author header is retained; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. No imported Lean or
Markdown file is modified.

This is an abstract topological-group result. It supplies no host
class-formation, cup-product, transfer, Tate-cohomology or reciprocity
theorem.
