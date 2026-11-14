# NYLL M040: a finite Galois subextension as a finite abstract field extension

The source is Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`
(file SHA-256 `c3b543d031492dac28deef22332941e7ff6bda845aa34e8be3ecd6c59d87098e`).
Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Original name | Source lines | Adapted name | Kind |
| --- | --- | --- | --- | --- |
| M040.023 | `ClassFormation.FiniteGaloisSubextension.toFiniteAbstractFieldExtension` | docstring 212–214, definition 215–222 | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.toFiniteAbstractFieldExtension` | def |

## The definition

**`FiniteGaloisSubextension.toFiniteAbstractFieldExtension`** (M040.023) is a
`noncomputable def`. Its universe is `u` (source line 27). Its binders, in
source order, are:

- implicit `{G : Type u}`, `[Group G]`, `[TopologicalSpace G]`, from the
  section variable (source line 31);
- implicit `{K : FiniteAbstractField G}`, a field finite over the
  distinguished base;
- explicit `(L : FiniteGaloisSubextension K.field)`, a finite Galois
  subextension of the closed subgroup `K.field`.

It returns a `FiniteAbstractFieldExtension G`. The section variable
`{K : ClosedSubgroup G}` of the source namespace (line 46) is shadowed by the
binder `{K : FiniteAbstractField G}`. It is kept, as in the source, and does
not enter the telescope. A focused `#check` confirms the telescope
`{G : Type u} → [Group G] → [TopologicalSpace G] → {K : FiniteAbstractField G} →
FiniteGaloisSubextension K.field → FiniteAbstractFieldExtension G`.

The body is the source tactic block, unchanged. It installs `L.finite` as a
local instance
`Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below)`
with `letI`, then returns
`FiniteAbstractFieldExtension.ofInclusion L.field K L.below`. So the top
endpoint is the `FiniteAbstractField` that `ofInclusion` builds on
`L.field`, with its finiteness over the distinguished base derived from the
quotient tower `L.field ≤ K.field ≤ baseField G`. The base endpoint is `K`,
the containment is `L.below`, and the relative finiteness is `L.finite`.
Normality of `L` is forgotten. A focused check confirms by `rfl` that the
definition equals
`@FiniteAbstractFieldExtension.ofInclusion G _ _ L.field K L.below L.finite`,
and that its top closed subgroup is `L.field` and its base is `K`.

## Reused Library declarations

These are imported by Lean name and not ported again:

- `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension` (M040.001), with
  its fields `field`, `below` and `finite`, from module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions`.
- `Langlands.NYLL.ClassFormation.FiniteAbstractField` (M010.121) and
  `Langlands.NYLL.ClassFormation.FiniteAbstractFieldExtension` (M010.130),
  reached through the module below.
- `Langlands.NYLL.ClassFormation.FiniteAbstractFieldExtension.ofInclusion`
  (M010.131), from module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.OfInclusion`.
  Its telescope is `(field : ClosedSubgroup G) (base : FiniteAbstractField G)
  (below : field.toSubgroup ≤ base.field.toSubgroup)
  [finiteQuotient : Finite (base.field.toSubgroup ⧸ extensionSubgroup base.field field below)]`,
  as in the source.
- `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002), the
  published abbreviation `L.toSubgroup.subgroupOf K.toSubgroup`. As in the
  source, it is written unqualified under `open CyclicCohomology` (source
  line 21).

## Modifications

Worker 171 made only these changes:

1. Only unit M040.023 is extracted. It goes into its own module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.AbstractExtension.Definitions`,
   because it needs `ofInclusion` (M010.131), which was published after the
   other M040 data in `FiniteGaloisSubextension.Definitions`.
2. The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
3. The source import
   `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient`
   is replaced by the two published modules named above.
4. `open KummerTheory` (source line 19) is dropped. The definition uses no
   name from that namespace, and with the two imports above no namespace
   `KummerTheory` is visible from `Langlands.NYLL.ClassFormation`, so the
   command fails with `unknown namespace` (checked).
5. The other source commands of the module are omitted. The source module
   docstring (lines 9–15) is replaced by a short docstring recording these
   modifications.

The surrounding scaffolding is kept: `namespace ClassFormation` (line 17),
`open CyclicCohomology` (21), `noncomputable section` (25), `universe u` (27),
`section GroupOnly` (29) with its variable (31), and
`namespace FiniteGaloisSubextension` (44) with its variable (46). The
declaration name, binders, the `noncomputable` modifier, the docstring and the
body are otherwise unchanged. A clean `lean_check` of the module, with no
errors or warnings, confirmed this.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation or reciprocity assertion.
