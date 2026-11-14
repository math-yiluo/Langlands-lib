# NYLL M296: the norm subgroup of a finite abelian subextension

Worker 449, 14 November 2026.

## Source

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
(file SHA-256 `f77cd402e62f7cd39a93a02269c2bfcffd9dc69b3919d352581a21d55aba67c0`),
scaffolding lines 30–34 and 404–411, definition lines 413–419. The body uses
`ClassFormation.finiteNormSubgroup` from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`
line 36 (inventory unit M039.001). Registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; attribution
supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The original
copyright and author header is retained; see `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.

## Name map

Adapted names carry the prefix `Langlands.NYLL.ClassFormation.`, original names
the prefix `ClassFormation.`; `FAS` abbreviates `FiniteAbelianSubextension`.

| Unit | Original name | Source lines | Adapted name | Kind |
| --- | --- | --- | --- | --- |
| M296.030 | `FAS.normSubgroup` | 413–419 | `FAS.normSubgroup` | def |

## Telescope and object

The source representation section is kept: `section Representation`
(line 404), the comment and
`variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (406–407),
`namespace FiniteAbelianSubextension` (409) and
`variable {K : ClosedSubgroup G}` (411). `IntegralRepGroupType` is the published
`Langlands.NYLL.IntegralRepGroupType`, the alias for `Type 0` that Mathlib's
`Rep ℤ G` requires. No `IsTopologicalGroup G`, compactness or other assumption is
added.

`normSubgroup (A : Rep ℤ G) (L : FAS K) : AddSubgroup (ambientFixedAddSubgroup A K)`,
with implicit `{G : IntegralRepGroupType}`, `[Group G]`, `[TopologicalSpace G]`
and implicit `{K : ClosedSubgroup G}`, is the norm subgroup `N_L = N_{L/K} A_L`
of the finite abelian extension `L | K`:

- the ambient group is the published `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup A K`,
  the additive subgroup of the coefficient module `A` fixed pointwise by
  `G_K`;
- the body, as in the source, installs the packaged finiteness
  `L.finite : Finite (K.toSubgroup ⧸ extensionSubgroup K L.field L.below)` as a
  local instance and returns `finiteNormSubgroup A K L.field L.below`, that is the
  range of the relative norm homomorphism `relativeNorm A K L.field L.below :
  ambientFixedAddSubgroup A L.field →+ ambientFixedAddSubgroup A K`.

So `normSubgroup A L` is definitionally
`@finiteNormSubgroup G _ _ A K L.field L.below L.finite`; the private harness
below checks this by `rfl`. The coefficient module's carrier universe is left
free, as in `Rep ℤ G` and the published `relativeNorm`.

The published objects used are `FiniteAbelianSubextension` with its abbreviations
`field`, `below` and `finite` (M296.001–.005), `Langlands.NYLL.CyclicCohomology.extensionSubgroup`
(M004.002), `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` (M023.001) and
`Langlands.NYLL.ClassFormation.finiteNormSubgroup` (M039.001).

## Modifications

1. The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`. The
   declaration name, binders, binder kinds, docstring, the comment on line 406
   and the tactic body are unchanged.
2. The source imports are replaced by the published finite abelian data module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions`
   and the published `finiteNormSubgroup` module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions`.
3. `universe u` and the `GroupOnly` section (lines 36–402) are omitted: the
   representation section does not use the universe `u`, and the `GroupOnly`
   declarations are in the sibling modules. The source line `open CyclicCohomology
   KummerTheory` is kept.
4. The module docstring is replaced by a modification note. As in the source,
   the `noncomputable section` is left open to the end of the file.
5. The source theorems of the same section (M296.031–.033, lines 421–470) are
   not part of this module; M296.031 and M296.032 are stated in the sibling
   module `FiniteAbelianSubextension/NormSubgroup/Statements`.

## Validation

The module compiles in the project Lean service (environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`) with no errors or warnings; its axioms
are `propext`, `Classical.choice` and `Quot.sound`. A private harness proves by
`rfl` that `normSubgroup A L` equals
`@finiteNormSubgroup G _ _ A K L.field L.below L.finite`. These checks establish
compilation and source correspondence only; independent review is still
required.
