# NYLL M077.024: `inertiaImage_normal`

## Exact target

The theorem
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.inertiaImage_normal`
has the telescope `{G : Type u} [Group G] [TopologicalSpace G]
{K : ClosedSubgroup G} (D : DegreeData G) (L : FiniteGaloisSubextension K)`
and type `inertiaImage_normalStatement D L`. That is the published target
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.inertiaImage_normalStatement`
of module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction.InertiaImage.Statements`.
The `[IsTopologicalGroup G]` section variable is omitted, as in the statement.
The target says that `L.inertiaImage D` is a normal subgroup of
`G(L/K) = G_K ⧸ G_L`. By definition (M077.023), `L.inertiaImage D` is the
image of `D.fieldInertiaWithin K` (the inertia group `I_K`, as the kernel
of the degree map restricted to `G_K`) under the quotient map
`QuotientGroup.mk' (extensionSubgroup K L.field L.below)`.

## Implemented proof

The proof is a single term, the source's:

1. `inferInstance : (D.fieldInertiaWithin K).Normal` finds the published
   instance `Langlands.NYLL.ClassFormation.DegreeData.fieldInertiaWithin_normal`
   (M010.015): `I_K` is normal in `G_K` because it is a kernel.
2. Mathlib's `Subgroup.Normal.map` sends a normal subgroup to a normal
   subgroup under a surjective homomorphism. It is applied to the quotient map
   `QuotientGroup.mk' (extensionSubgroup K L.field L.below)` with
   surjectivity `QuotientGroup.mk'_surjective`.
3. The result has type
   `((D.fieldInertiaWithin K).map (QuotientGroup.mk' …)).Normal`. This is
   definitionally `inertiaImage_normalStatement D L`, after unfolding the
   statement wrapper and `inertiaImage`, so `exact` closes the goal.

## Dependencies

- Imported published module:
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction.InertiaImage.Statements`.
  Through its imports it provides the target, `inertiaImage` (M077.023),
  `FiniteGaloisSubextension` (M040.001), `extensionSubgroup` (M004.002),
  `DegreeData.fieldInertiaWithin` (M010.014) and the instance
  `DegreeData.fieldInertiaWithin_normal` (M010.015).
- Mathlib: `Subgroup.Normal.map`, `QuotientGroup.mk'` and
  `QuotientGroup.mk'_surjective`.
- No unpublished result is used and no helper declaration is added.
- Axioms reported by the Lean service: `propext`, `Classical.choice` and
  `Quot.sound` only.

## Source and modifications

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Reduction.lean`
(file SHA-256 `42b99923f18b24748b529f410725f5a763554010151f57e0f8c0c5d943acf613`),
lines 471–479 (M077.024): `omit [IsTopologicalGroup G] in` at 471, the docstring at
472–473, the telescope and statement at 474–475 and the proof at 475–479.
The readable pinned source is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Its registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement`
(`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

Modifications by Worker 756, 16 November 2026:

- The namespace is prefixed with `Langlands.NYLL`. The source imports are
  replaced by the published statement module above, and the unused
  `open KummerTheory` is dropped.
- The theorem's type `(L.inertiaImage D).Normal` is written as the
  published `inertiaImage_normalStatement D L`. The section `GroupOnly`,
  its variables, `omit [IsTopologicalGroup G] in`, the docstring and the
  proof term are unchanged.
- The rest of the source file is omitted. This includes the instance
  `inertiaImage_normalInstance` that follows the theorem.

The original copyright and author header is retained; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. No imported Lean or
Markdown file is modified.

This is an abstract group-theoretic result about degree data. It supplies
no host class-formation, cup-product, transfer, Tate-cohomology or
reciprocity theorem.
