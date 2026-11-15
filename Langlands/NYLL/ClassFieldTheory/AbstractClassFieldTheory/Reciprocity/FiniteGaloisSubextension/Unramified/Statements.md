# NYLL M040.021: the inertia criterion for unramified finite Galois extensions

The paired Lean file adapts the statements of one theorem of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`.
The pinned source file has SHA-256
`c3b543d031492dac28deef22332941e7ff6bda845aa34e8be3ecd6c59d87098e`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.FiniteGaloisSubextension.` | Docstring | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.` |
| --- | --- | --- | --- | --- | --- |
| M040.021 | `isUnramified_iff_inertia_le` | 197 | 198–201 | 201–202 | `isUnramified_iff_inertia_leStatement` |

The source imports
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient`
(line 7). The context of the theorem is `namespace ClassFormation`
(line 17), `open KummerTheory` (line 19), `open CyclicCohomology`
(line 21), `noncomputable section` (line 25), `universe u` (line 27),
`section GroupOnly` (line 29), the variables
`{G : Type u} [Group G] [TopologicalSpace G]` (line 31),
`namespace FiniteGaloisSubextension` (line 44) and the variable
`{K : ClosedSubgroup G}` (line 46).

The other declarations of the source file are not part of this module. The
statement uses Mathlib's `ClosedSubgroup` with `toSubgroup`, subgroup
infimum `⊓` and order `≤`, `ContinuousMonoidHom.toMonoidHom` and
`MonoidHom.ker`, and these published NYLL declarations:

- `Langlands.NYLL.ClassFormation.DegreeData` (M010.002), with its field
  `degree`;
- `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension` (M040.001), with
  its field `field`, and `FiniteGaloisSubextension.IsUnramified` (M040.005),
  defined as the unramified predicate of the underlying finite abstract
  extension, from `Reciprocity.FiniteGaloisSubextension.Definitions`.

## Target and complete telescope

The target has, before the binders shown, the binders of the source
variable lines 31 and 46: implicit `{G : Type u}`, the instances
`[Group G]` and `[TopologicalSpace G]`, and implicit
`{K : ClosedSubgroup G}`.

### M040.021

```lean
def isUnramified_iff_inertia_leStatement (L : FiniteGaloisSubextension K)
    (D : DegreeData G) : Prop :=
    L.IsUnramified D ↔
      K.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ L.field.toSubgroup
```

A finite Galois subextension `L` of `K` is unramified for `D` exactly when
the inertia subgroup of `K` is contained in the subgroup representing
`L.field`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the targets lie in
   `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension`.
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
4. Replace the source import by
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions`,
   which publishes `FiniteGaloisSubextension` and its predicate
   `IsUnramified` and imports the module of `DegreeData`.
5. Omit the other declarations of the source file and the opens of
   `KummerTheory` and `CyclicCohomology`: no name of those namespaces occurs
   in the statement. Retain the namespaces, the noncomputable section, the
   universe declaration, the section `GroupOnly` and the variable lines 31
   and 46.
6. No linter option is needed: every binder occurs in the proposition. No
   helper declaration or instance is added.

This is an exact source statement as a named proposition, without a
published proof. It discharges no host class-formation, cup, transfer, Tate
or reciprocity target.

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
