# NYLL M077.024: normality of the inertia image

The paired Lean file adapts the statement of the theorem `inertiaImage_normal` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Reduction.lean`.
The pinned source file has SHA-256
`42b99923f18b24748b529f410725f5a763554010151f57e0f8c0c5d943acf613`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.FiniteGaloisSubextension.` | `omit` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- | --- |
| M077.024 | `inertiaImage_normal` | 471 | 472–473 | 474–475 | 475–479 | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.inertiaImage_normalStatement` |

The enclosing source context is `namespace ClassFormation` (line 25),
`open KummerTheory` (line 27), `open CyclicCohomology` (line 29),
`noncomputable section` (line 33), `universe u` (line 35),
`section GroupOnly` (lines 222–594), the variables
`{G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]`
(line 224), `namespace FiniteGaloisSubextension` (line 226) and
`variable {K : ClosedSubgroup G}` (line 228). Line 471 is `omit [IsTopologicalGroup G] in`, so the source
theorem does not take the topological-group instance.

The names used resolve to `Langlands.NYLL` declarations: `DegreeData`
(M010.002), `FiniteGaloisSubextension K` (M040.001) with its quotient
`extensionQuotient` (M040.004) and the group instance M040.008, and
`FiniteGaloisSubextension.inertiaImage` (M077.023, from the sibling module
`Reciprocity.Reduction.InertiaImage.Definitions`), the image of the inertia
subgroup `I_K ≤ G_K` in `G(L/K) = G_K ⧸ G_L`. `Subgroup.Normal` is
Mathlib's.

## Target and complete telescope

The target has the binders implicit `{G : Type u}`, `[Group G]`,
`[TopologicalSpace G]` and implicit `{K : ClosedSubgroup G}`, followed by:

```lean
def inertiaImage_normalStatement (D : DegreeData G)
    (L : FiniteGaloisSubextension K) : Prop :=
    (L.inertiaImage D).Normal
```

For degree data `D` and a finite Galois extension `L | K`, the image of
`I_K` in `G(L/K)` is a normal subgroup.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace `theorem inertiaImage_normal … : statement := proof` by
   `def inertiaImage_normalStatement … : Prop := statement`. The statement
   is copied verbatim. The source proof is omitted: this contribution
   publishes the proposition target, and its proof is separate work. (The
   source instance M077.025 `inertiaImage_normalInstance`, whose body is
   this theorem, is not part of this contribution.)
3. Prefix the source docstring with `Target:`. Replace the source module
   docstring by a description of this module with a modification notice
   that names the source theorem.
4. Replace the source imports by the sibling module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction.InertiaImage.Definitions`
   (M077.023 and its imports).
5. Omit the rest of the source file and the unused `open KummerTheory`.
   Retain `open CyclicCohomology`, the noncomputable section, the universe,
   the section `GroupOnly`, its variable lines, the namespace and the
   `omit [IsTopologicalGroup G] in`.
6. No helper declaration or instance is added.

These are exact source statements as named propositions, without
published proofs. They discharge no host class-formation, cup, transfer,
Tate or reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
