# NYLL M080.008–M080.009: equal restrictions in finite Galois towers

The paired Lean file adapts the statements of the theorems `commute_of_same_restriction_of_inertia_le` and `relativeCosetAction_eq_of_restriction_eq` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionCosets.lean`.
The pinned source file has SHA-256
`c355b25591d40a48d3cf642a1015ae1f5b49d9a14df8a05516a2128c2b43856f`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.FiniteGaloisSubextension.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M080.008 | `commute_of_same_restriction_of_inertia_le` | 323–324 | 325–339 | 339–407 | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.commute_of_same_restriction_of_inertia_leStatement` |
| M080.009 | `relativeCosetAction_eq_of_restriction_eq` | 409–410 | 411–427 | 427–441 | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.relativeCosetAction_eq_of_restriction_eqStatement` |

The enclosing source context is `noncomputable section` (line 18),
`namespace ClassFormation` (line 20), `open KummerTheory` (line 22),
`open CyclicCohomology` (line 23), the comment and variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (lines 25–26)
and `namespace FiniteGaloisSubextension` (lines 28–443). The only source
import is the unported module
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction`
(line 7).

The names used resolve to `Langlands.NYLL` declarations:

- `IntegralRepGroupType` (M002.001), the abbreviation `Type 0`;
- `DegreeData` (M010.002) and `DegreeData.fieldInertia` (M010.012, both
  from `Degree.Fields.Definitions`), where `D.fieldInertia K = K ⊓ D.inertia`
  is the closed subgroup `I_K` of inertia elements of `G_K`;
- `DegreeData.AbstractExtension G` (M010.028, from
  `Degree.Fields.AbstractExtension.Definitions`), a pair of closed subgroups
  `E.field` and `E.base` with `E.below : E.field.toSubgroup ≤ E.base.toSubgroup`,
  representing an extension of fields `E.field | E.base` contravariantly;
- `FiniteGaloisSubextension K` (M040.001) with fields `M.field` and
  `M.below`;
- `CyclicCohomology.extensionSubgroup` (M004.002), the abbreviation
  `extensionSubgroup K L hLK = L.toSubgroup.subgroupOf K.toSubgroup`;
- `abstractReciprocityRestriction` (M075.005), the restriction
  `G_K ⧸ G_L →* G_K ⧸ G_M` for `G_L ≤ G_M ≤ G_K` with both normal in `G_K`;
- `KummerTheory.ambientFixedAddSubgroup` (M023.001, from
  `GaloisCohomology.Kummer.Abstract.KummerDelta.U001.Definitions`), the
  additive subgroup `A^{G_L}` of elements of `A` fixed by `G_L`;
- `fixedFieldInclusion` (M028.001, from `Degree.PrimeElements.Definitions`),
  the inclusion `A^{G_K} →+ A^{G_L}` for `G_L ≤ G_K`;
- `relativeCosetAction` (M024.001, from `Degree.Norm.Definitions`): for
  `a ∈ A^{G_L}` and `q ∈ G_K ⧸ G_L`, the element `ρ(k) a` of `A` for any
  representative `k` of `q`.

`Rep ℤ G`, `IsTopologicalGroup`, `Subgroup.Normal` and `Commute` are
Mathlib's.

## Targets and complete telescopes

Both targets have the binders implicit `{G : IntegralRepGroupType}`,
`[Group G]` and `[TopologicalSpace G]`, followed by those shown. Write
`K = E.base` and `G_K`, `G_E`, `G_M` for the subgroups `E.base`, `E.field`
and `M.field`.

### M080.008

```lean
def commute_of_same_restriction_of_inertia_leStatement
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    (hIE : (D.fieldInertia E.field).toSubgroup ≤ M.field.toSubgroup)
    [hEnormal :
      (extensionSubgroup E.base E.field E.below).Normal]
    (g t : E.base.toSubgroup ⧸
      extensionSubgroup E.base M.field M.below)
    (hres : abstractReciprocityRestriction
        E.base E.field M.field hME E.below g =
      abstractReciprocityRestriction
        E.base E.field M.field hME E.below t) : Prop :=
    Commute g t
```

Let `E | K` be an extension with `G_E` normal in `G_K`, and `M` a finite
Galois extension of `K` with `G_M ≤ G_E` (so the field `M` contains `E`)
and `I_E ≤ G_M`. If two elements `g, t` of `G(M/K) = G_K ⧸ G_M` have the
same image in `G_K ⧸ G_E`, then `g * t = t * g`.

### M080.009

```lean
def relativeCosetAction_eq_of_restriction_eqStatement
    (A : Rep ℤ G) (E : DegreeData.AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    [hEnormal :
      (extensionSubgroup E.base E.field E.below).Normal]
    (a : ambientFixedAddSubgroup A E.field)
    (g t : E.base.toSubgroup ⧸
      extensionSubgroup E.base M.field M.below)
    (hres : abstractReciprocityRestriction
        E.base E.field M.field hME E.below g =
      abstractReciprocityRestriction
        E.base E.field M.field hME E.below t) : Prop :=
    relativeCosetAction A E.base M.field M.below
        (fixedFieldInclusion A E.field M.field hME a) g =
      relativeCosetAction A E.base M.field M.below
        (fixedFieldInclusion A E.field M.field hME a) t
```

With `E`, `M` and `hME` as above (no inertia hypothesis), let
`a ∈ A^{G_E}`. If `g, t ∈ G_K ⧸ G_M` have the same image in `G_K ⧸ G_E`,
then acting by representatives of `g` and of `t` on `a`, viewed in
`A^{G_M}`, gives the same element of `A`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. Each statement is copied
   verbatim. The source proofs are omitted: this contribution publishes the
   proposition targets, and their proofs are separate work.
3. Prefix each source docstring with `Target:`. Replace the source module
   docstring by a description of this module with a modification notice
   that names the source theorems.
4. Put `set_option linter.unusedVariables false in` before each target. The
   propositions do not mention the binders `hEnormal`, `hIE` and `hres`, and
   the linter would otherwise warn; the option changes no declaration.
5. Replace the source import by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions`
   (M040.001, M004.002),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.Definitions`
   (M075.005),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.Definitions`
   (M010.028, which also brings M010.002 and M010.012),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.Definitions`
   (M024.001, which also brings M023.001),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Definitions`
   (M028.001) and `Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse`
   (M002.001).
6. Omit the other declarations of the source file. Retain the
   noncomputable section, both `open` lines, the comment, the variable line
   and the namespaces.
7. No helper declaration or instance is added.

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
