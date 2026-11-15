# NYLL M077.023: the inertia image in a finite Galois quotient

The paired Lean file adapts the definition `inertiaImage` of Naganori
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

| Unit | Source definition after `ClassFormation.FiniteGaloisSubextension.` | Docstring | Declaration | Adapted declaration |
| --- | --- | --- | --- | --- |
| M077.023 | `inertiaImage` | 464–465 | 466–469 | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.inertiaImage` |

The enclosing source context is `namespace ClassFormation` (line 25),
`open KummerTheory` (line 27), `open CyclicCohomology` (line 29),
`noncomputable section` (line 33), `universe u` (line 35),
`section GroupOnly` (lines 222–594), the variables
`{G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]`
(line 224), `namespace FiniteGaloisSubextension` (line 226) and
`variable {K : ClosedSubgroup G}` (line 228). The rest of the source file is not part of this module; the
statement of the next source theorem, M077.024 `inertiaImage_normal`, is in
the sibling module `Reciprocity.Reduction.InertiaImage.Statements`.

The names used resolve to `Langlands.NYLL` declarations:

- `DegreeData` (M010.002, from `Degree.Fields.Definitions`), with
  `DegreeData.fieldInertiaWithin` (M010.014, same module): for a closed
  subgroup `K`, the inertia subgroup `I_K` inside `G_K`, defined as the
  kernel of the degree map restricted to `G_K`;
- `FiniteGaloisSubextension K` (M040.001) with fields `L.field` and
  `L.below`, and `FiniteGaloisSubextension.extensionQuotient` (M040.004),
  the quotient `G(L/K) = G_K ⧸ G_L`, whose group instance (M040.008) and
  normality instance (M040.007) are in
  `Reciprocity.FiniteGaloisSubextension.Definitions`;
- `CyclicCohomology.extensionSubgroup` (M004.002), the abbreviation
  `L.toSubgroup.subgroupOf K.toSubgroup`.

`Subgroup.map` and `QuotientGroup.mk'` are Mathlib's.

## Definition

The definition has the binders implicit `{G : Type u}`, `[Group G]`,
`[TopologicalSpace G]` and implicit `{K : ClosedSubgroup G}`, followed by:

```lean
def inertiaImage (D : DegreeData G) (L : FiniteGaloisSubextension K) :
    Subgroup L.extensionQuotient :=
  (D.fieldInertiaWithin K).map
    (QuotientGroup.mk' (extensionSubgroup K L.field L.below))
```

For degree data `D` and a finite Galois extension `L | K`, the image of
the inertia subgroup `I_K ≤ G_K` under the quotient map
`G_K → G(L/K) = G_K ⧸ G_L`. Although the section variable line declares
`[IsTopologicalGroup G]`, Lean does not add this instance to the
definition, because neither its type nor its body uses it; a project Lean
service `#check` shows the signature above. The same holds for the source,
whose next theorem uses `inertiaImage` after
`omit [IsTopologicalGroup G] in`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace the source imports by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions`
   (M040.001, M040.004, M040.007, M040.008 and M004.002) and
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`
   (M010.002, M010.014).
3. Replace the source module docstring by a description of this module with
   a modification notice that names the source definition. Omit the section
   heading comment at line 462.
4. Omit the rest of the source file and the unused `open KummerTheory`.
   Retain `open CyclicCohomology` (for `extensionSubgroup`), the
   noncomputable section, the universe, the section `GroupOnly`, its
   variable lines and the namespace.
5. The binders, docstring and body are unchanged (the docstring keeps the
   source's incomplete phrase "in the notation of."). No helper declaration
   or instance is added.

This definition discharges no host class-formation, cup, transfer, Tate or
reciprocity target.

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
