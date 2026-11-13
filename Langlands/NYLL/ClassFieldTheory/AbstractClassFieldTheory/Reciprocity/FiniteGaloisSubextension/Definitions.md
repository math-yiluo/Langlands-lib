# NYLL M040: finite Galois subextension data

The source is Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`
(file SHA-256 `c3b543d031492dac28deef22332941e7ff6bda845aa34e8be3ecd6c59d87098e`).
Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Name map

All adapted names use the prefix `Langlands.NYLL.ClassFormation.`, and all
original names the prefix `ClassFormation.`. Below, `FGS` abbreviates
`FiniteGaloisSubextension` in both columns.

| Unit | Original name | Source lines | Adapted name | Kind |
| --- | --- | --- | --- | --- |
| M040.001 | `FGS` | 34–42 | `FGS` | structure |
| M040.002 | `FGS.toGaloisSubextension` | 49–53 | `FGS.toGaloisSubextension` | def |
| M040.003 | `FGS.toFiniteAbstractExtension` | 58–63 | `FGS.toFiniteAbstractExtension` | def |
| M040.004 | `FGS.extensionQuotient` | 67–68 | `FGS.extensionQuotient` | def |
| M040.005 | `FGS.IsUnramified` | 71–72 | `FGS.IsUnramified` | def |
| M040.006 | `FGS.IsTotallyRamified` | 75–77 | `FGS.IsTotallyRamified` | def |
| M040.007 | `FGS.extensionSubgroup_normalInstance` | 80–82 | `FGS.extensionSubgroup_normalInstance` | instance |
| M040.008 | `FGS.extensionQuotient_groupInstance` | 86–90 | `FGS.extensionQuotient_groupInstance` | instance |
| M040.009 | `FGS.extensionQuotient_finiteInstance` | 93–95 | `FGS.extensionQuotient_finiteInstance` | instance |
| M040.010 | `FGS.extensionQuotientMulEquiv` | 99–102 | `FGS.extensionQuotientMulEquiv` | def |
| M040.011 | `FGS.extensionQuotientMk` | 105–107 | `FGS.extensionQuotientMk` | def |
| M040.015 | `FGS.toGaloisExtensionQuotientMulEquiv` | 151–154 | `FGS.toGaloisExtensionQuotientMulEquiv` | def |
| M040.028 | `FGS.refl` | 340–356 | `FGS.refl` | def |
| M040.029 | `FGS.compositum` | 359–398 | `FGS.compositum` | def |

M040.029 is not in the task's lexical list. It is ported here because the
listed targets M040.030 and M040.031 (`compositum_le_left`,
`compositum_le_right`) mention `L₁.compositum L₂`, and the task requires
unlisted declarations of the same source module that listed units need to be
ported with them.

## Telescope and objects

The surrounding source scaffolding is kept: `namespace ClassFormation`
(line 17), `open CyclicCohomology` (21), `noncomputable section` (25),
`universe u` (27), `section GroupOnly` (29) with
`variable {G : Type u} [Group G] [TopologicalSpace G]` (31), and
`namespace FiniteGaloisSubextension` (44) with
`variable {K : ClosedSubgroup G}` (46).

- The structure has implicit `{G : Type u}`, `[Group G]`,
  `[TopologicalSpace G]`, explicit `(K : ClosedSubgroup G)`, and the four
  source fields in source order: `field : ClosedSubgroup G`,
  `below : field.toSubgroup ≤ K.toSubgroup`,
  `normal : (extensionSubgroup K field below).Normal`, and
  `finite : Finite (K.toSubgroup ⧸ extensionSubgroup K field below)`.
- Every namespace definition and instance has implicit `{G : Type u}`,
  `[Group G]`, `[TopologicalSpace G]`, implicit `{K : ClosedSubgroup G}`, then
  explicit `(L : FiniteGaloisSubextension K)`; the two predicates add explicit
  `(D : DegreeData G)` after `L`. `refl` instead takes explicit
  `(K : ClosedSubgroup G)`, and `compositum` takes explicit
  `(L₁ L₂ : FiniteGaloisSubextension K)`.
- `toGaloisSubextension` builds the published
  `DegreeData.GaloisSubextension K` from `field`, `below`, `normal`;
  `toFiniteAbstractExtension` builds the published
  `DegreeData.FiniteAbstractExtension G` with `field := L.field`,
  `base := K`, `below := L.below`, `finiteQuotient := L.finite`.
- `extensionQuotient` is a `def : Type u` equal to
  `K.toSubgroup ⧸ extensionSubgroup K L.field L.below`. The predicates are
  the published `FiniteAbstractExtension.IsUnramified` and
  `FiniteAbstractExtension.IsTotallyRamified` of `L.toFiniteAbstractExtension`.
- The three instances are the source ones, in the same scope: the normal
  subgroup instance is `L.normal`; the group instance unfolds the named
  quotient by `change` and uses Mathlib's quotient group; the finiteness
  instance is `L.finite`. No other instance is added.
- `extensionQuotientMulEquiv` is `MulEquiv.refl _`, `extensionQuotientMk` is
  `QuotientGroup.mk' (extensionSubgroup K L.field L.below)`, and
  `toGaloisExtensionQuotientMulEquiv` is
  `L.extensionQuotientMulEquiv.trans L.toGaloisSubextension.extensionQuotientMulEquiv.symm`,
  using the published `DegreeData.GaloisSubextension.extensionQuotientMulEquiv`.
- `refl K` has `field := K`, `below := le_rfl` and the source `normal` and
  `finite` proofs (rewrite `extensionSubgroup K K le_rfl` to `⊤`).
- `compositum L₁ L₂` has `field := L₁.field ⊓ L₂.field`,
  `below := fun _ h => L₁.below h.1`, and the source `normal` and `finite`
  proofs through the equality of the compositum subgroup with
  `extensionSubgroup K L₁.field L₁.below ⊓ extensionSubgroup K L₂.field L₂.below`.

## Reused Library declarations

- `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002, source
  `Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean` line 51, file SHA-256
  `06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`), the
  published abbreviation `L.toSubgroup.subgroupOf K.toSubgroup` with the
  source telescope. It is used under its own name, so the source spelling
  `extensionSubgroup K L hLK` is kept everywhere.
- `Langlands.NYLL.ClassFormation.DegreeData` (M010.002),
  `DegreeData.GaloisSubextension` (M010.052) with its
  `extensionQuotientMulEquiv` (M010.059), and
  `DegreeData.FiniteAbstractExtension` (M010.065) with its `IsUnramified`
  (M010.071) and `IsTotallyRamified` (M010.072).

## Modifications

Worker 4918 made only these changes:

1. The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
2. The source import
   `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient`
   is replaced by the three published modules
   `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`,
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.GaloisSubextension.Definitions`
   and
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.Definitions`.
3. `open KummerTheory` (line 19) is dropped: no ported declaration uses a
   name from it except as noted in item 4, and no
   `Langlands.NYLL.ClassFormation.KummerTheory` or `Langlands.NYLL.KummerTheory`
   namespace is imported, so the command would not elaborate.
4. Inside the `simp only` calls of the two proof fields `normal` and `finite`
   of `compositum` (source lines 369 and 385), the source lemma
   `KummerTheory.mem_extensionSubgroup_iff` (from
   `Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianAssembly.lean`,
   lines 33–38, file SHA-256
   `ca4ad38a7ed46fa029400e2c7718faf0587b4206731c82c8c45d6839b719f54c`,
   proved by `Iff.rfl` and not published) is replaced by Mathlib's
   `Subgroup.mem_subgroupOf`, the corresponding membership lemma for the
   abbreviation's body. Only proofs of propositions change, so the
   constructed structure is unchanged by proof irrelevance.
5. The source theorem commands of the module, and the source data
   commands not in the table above (lines 158–338 and the
   `Representation` section, lines 414–477), are omitted here. The listed
   theorems M040.012–014, 018, 020, 022, 024, 025, 030 and 031 are stated as
   Prop-valued targets in the sibling `Statements` module.
6. The source module docstring (lines 9–15) is replaced by a short
   docstring recording these modifications.

Declarations, binders, docstrings and all other bodies are otherwise
unchanged; this was confirmed by a clean `lean_check` of the module.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation or reciprocity assertion.
