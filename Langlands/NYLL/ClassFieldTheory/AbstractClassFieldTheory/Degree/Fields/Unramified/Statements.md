# NYLL M010.046, .063, .075: the inertia criterion for unramified extensions

The paired Lean file adapts the statements of three theorems of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`.
The pinned source file has SHA-256
`841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.DegreeData.` | Docstring | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.ClassFormation.DegreeData.` |
| --- | --- | --- | --- | --- | --- |
| M010.046 | `AbstractExtension.isUnramified_iff_inertia_le` | 385–387 | 388–390 | 390–391 | `AbstractExtension.isUnramified_iff_inertia_leStatement` |
| M010.063 | `GaloisSubextension.isUnramified_iff_inertia_le` | 535 | 536–539 | 539–540 | `GaloisSubextension.isUnramified_iff_inertia_leStatement` |
| M010.075 | `FiniteAbstractExtension.isUnramified_iff_inertia_le` | 626–627 | 628–630 | 630–631 | `FiniteAbstractExtension.isUnramified_iff_inertia_leStatement` |

The source imports `Mathlib.GroupTheory.QuotientGroup.Basic`,
`Nyll.GaloisCohomology.Cyclic.IntegralRepUniverse`,
`Nyll.GaloisCohomology.Cyclic.NormKernelVanishing`,
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices` and
`Nyll.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger` (lines 7–11).
The context of the three theorems is `namespace ClassFormation` (line 22),
`open CyclicCohomology` (line 24), `noncomputable section` (line 28),
`universe u` (line 30), the variables
`{G : Type u} [Group G] [TopologicalSpace G]` (line 46),
`namespace DegreeData` (line 217) and then

- for M010.046, `namespace AbstractExtension` (line 231);
- for M010.063, `namespace GaloisSubextension` (line 467) with the variable
  `{K : ClosedSubgroup G}` (line 469);
- for M010.075, `namespace FiniteAbstractExtension` (line 565) with the
  variable `(E : FiniteAbstractExtension G)` (line 567).

The other declarations of the source file are not part of this module. The
statements use Mathlib's `ClosedSubgroup` with `toSubgroup`, subgroup
infimum `⊓` and order `≤`, `ContinuousMonoidHom.toMonoidHom` and
`MonoidHom.ker`, and these published NYLL declarations:

- `Langlands.NYLL.ClassFormation.DegreeData` (M010.002), with its field
  `degree : G →ₜ* ZHatMul`;
- `DegreeData.AbstractExtension` (M010.028), with its fields `field` and
  `base`, and `DegreeData.AbstractExtension.IsUnramified` (M010.044), from
  `Degree.Fields.AbstractExtension.Definitions` and
  `Degree.Fields.AbstractExtension.StructuralDefinitions`;
- `DegreeData.GaloisSubextension` (M010.052), with its field `field`, and
  `DegreeData.GaloisSubextension.IsUnramified` (M010.055), from
  `Degree.Fields.GaloisSubextension.Definitions`;
- `DegreeData.FiniteAbstractExtension` (M010.065), which extends
  `AbstractExtension` and so has the fields `field` and `base`, and
  `DegreeData.FiniteAbstractExtension.IsUnramified` (M010.071), from
  `Degree.Fields.FiniteExtension.Definitions`.

The published `AbstractExtension.IsUnramified E D` is by definition the
containment `E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup`;
the other two predicates are that of the underlying abstract extension.

## Targets and complete telescopes

Each target has, before the binders shown, the binders of the source
variable line 46: implicit `{G : Type u}` and the instances `[Group G]` and
`[TopologicalSpace G]`.

### M010.046

```lean
def isUnramified_iff_inertia_leStatement (E : AbstractExtension G) (D : DegreeData G) : Prop :=
    E.IsUnramified D ↔
      E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup
```

An abstract extension `E` is unramified for `D` exactly when the inertia
subgroup of its base, the kernel of the degree map intersected with
`E.base`, is contained in the subgroup representing `E.field`.

### M010.063

After the source variable binder implicit `{K : ClosedSubgroup G}`:

```lean
def isUnramified_iff_inertia_leStatement (L : GaloisSubextension K)
    (D : DegreeData G) : Prop :=
    L.IsUnramified D ↔
      K.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ L.field.toSubgroup
```

A Galois subextension `L` of `K` is unramified for `D` exactly when the
inertia subgroup of `K` is contained in the subgroup representing
`L.field`.

### M010.075

After the source variable binder explicit `(E : FiniteAbstractExtension G)`:

```lean
def isUnramified_iff_inertia_leStatement (D : DegreeData G) : Prop :=
    E.IsUnramified D ↔
      E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup
```

A finite abstract extension is unramified for `D` exactly when the inertia
subgroup of its base is contained in the subgroup representing its field.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the targets lie in
   `Langlands.NYLL.ClassFormation.DegreeData`.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The telescopes and the
   statements are copied verbatim, including the binder names, kinds and
   order; `: Prop :=` is appended to the last telescope line, and the line
   breaks are otherwise those of the source. The source proofs are omitted:
   this contribution publishes the proposition targets, and their proofs
   are separate work.
3. Prefix each source docstring with `Target:` and lower-case the first word
   after it; the wording is otherwise unchanged, and the lines are
   rewrapped. Replace the source module docstring by a description of this
   module with a modification notice that names the source theorems.
4. Replace the five source imports by
   `Degree.Fields.GaloisSubextension.Definitions` and
   `Degree.Fields.FiniteExtension.Definitions` (under
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory`), which
   publish `GaloisSubextension`, `FiniteAbstractExtension` and their
   predicates and import the modules of `DegreeData`, `AbstractExtension`
   and `AbstractExtension.IsUnramified`.
5. Omit the other declarations of the source file and the open of
   `CyclicCohomology`: no name of that namespace occurs in the three
   statements. Retain the namespaces, the noncomputable section, the
   universe declaration and the variable lines 46, 469 and 567.
6. No linter option is needed: every binder occurs in its proposition. No
   helper declaration or instance is added.

These are exact source statements as named propositions, without published
proofs. They discharge no host class-formation, cup, transfer, Tate or
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
