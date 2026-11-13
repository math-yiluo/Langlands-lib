# NYLL M010: finite extensions between fields finite over the base

The source is Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`
(file SHA-256 `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`).
Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

All public names in the table use prefix `Langlands.NYLL.ClassFormation.`,
unless written in full. Original names use prefix `ClassFormation.`.

| Unit | Original name | Source lines | Adapted name |
| --- | --- | --- | --- |
| M010.130 | `FiniteAbstractFieldExtension` | 1199–1214 | `FiniteAbstractFieldExtension` |
| M010.132 | `FiniteAbstractFieldExtension.toFiniteAbstractExtension` | 1255–1262 | `FiniteAbstractFieldExtension.toFiniteAbstractExtension` |
| M010.133 | `FiniteAbstractFieldExtension.IsUnramified` | 1264–1267 | `FiniteAbstractFieldExtension.IsUnramified` |
| M010.134 | `FiniteAbstractFieldExtension.IsTotallyRamified` | 1269–1272 | `FiniteAbstractFieldExtension.IsTotallyRamified` |
| M010.135 | `FiniteAbstractFieldExtension.degree` | 1274–1276 | `FiniteAbstractFieldExtension.degree` |
| M010.139 | anonymous `instance` in namespace `FiniteAbstractFieldExtension` | 1296–1301 | `Langlands.NYLL.PortInternal.M010.d139` |

**`FiniteAbstractFieldExtension`** (M010.130) keeps the explicit binders
`(G : Type u) [Group G] [TopologicalSpace G]` and exactly the four source
fields: `field : FiniteAbstractField G` (top endpoint), `base :
FiniteAbstractField G` (base endpoint), the containment
`below : field.field.toSubgroup ≤ base.field.toSubgroup`, and the proof field
`finiteQuotient : Finite (base.field.toSubgroup ⧸ extensionSubgroup base.field
field.field below)`. Thus both endpoints carry their own finiteness over the
distinguished base, and the relative quotient `G_K / G_L` is finite.

The namespace definitions take implicit `{G : Type u}` with its two instances
from the section variable and explicit `(E : FiniteAbstractFieldExtension G)`:

- **`toFiniteAbstractExtension`** (M010.132), attribute `@[implicit_reducible]`
  as in the source, returns the published
  `DegreeData.FiniteAbstractExtension G` with `field := E.field.field`,
  `base := E.base.field`, `below := E.below`,
  `finiteQuotient := E.finiteQuotient`.
- **`IsUnramified`** (M010.133), attribute `@[implicit_reducible]` as in the
  source, with explicit `(D : DegreeData G)` after `E`, is the published
  `E.toFiniteAbstractExtension.IsUnramified D`.
- **`IsTotallyRamified`** (M010.134), same binders, no attribute, is the
  published `E.toFiniteAbstractExtension.IsTotallyRamified D`.
- **`degree`** (M010.135) is `noncomputable def degree … : ℕ+ :=
  E.toFiniteAbstractExtension.degree`, i.e. the published positive degree
  `Nat.card` of the stored finite relative quotient.

**`PortInternal.M010.d139`** (M010.139) is the source anonymous instance
`(E : FiniteAbstractFieldExtension G) : Finite (E.base.field.toSubgroup ⧸
extensionSubgroup E.base.field E.field.field E.below)` with body
`E.finiteQuotient`. It is declared inside namespace
`Langlands.NYLL.ClassFormation.FiniteAbstractFieldExtension` with the explicit
`_root_.Langlands.NYLL.PortInternal.M010.d139` name, keeping the source scope,
binders and instance type. It is the only instance added; its class argument is
the quotient by projections of the new structure, so it cannot conflict with
Mathlib or Library instances.

Source declarations of this namespace that are not in this module:
`ofInclusion` (M010.131, lines 1218–1253) is deferred until the
`AbstractExtension.Tower.degreeCardinal_mul` proof it uses is published;
`residueDegree` (M010.136, lines 1278–1281), `ramificationIndex`
(lines 1283–1286), the theorem `residueDegree_eq_degree_of_isUnramified`
(M010.138, lines 1288–1294) and `toFiniteResidueAbstractExtension`
(M010.140, lines 1303–1310) depend on data not yet published. None of the
declarations here uses them.

Used published declarations (imported by name):
`Langlands.NYLL.ClassFormation.FiniteAbstractField` (M010.121, module
`Degree.Fields.FiniteAbstractField.Definitions`),
`Langlands.NYLL.ClassFormation.DegreeData` (M010.002),
`Langlands.NYLL.ClassFormation.DegreeData.FiniteAbstractExtension` with its
`IsUnramified`, `IsTotallyRamified` and `degree` (M010.065/.071/.072/.085,
module `Degree.Fields.FiniteExtension.Definitions`, reached through the
single import `Degree.Fields.FiniteAbstractField.Definitions`), and
`Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002). As in the
source, `extensionSubgroup` is written under `open CyclicCohomology` (source
line 24), now resolving to the published `Langlands.NYLL.CyclicCohomology`
abbreviation with body `L.toSubgroup.subgroupOf K.toSubgroup`, so the terms are
those of the source.

Modifications by Worker 171: only units M010.130, M010.132–135 and M010.139 are
extracted; the namespace is prefixed with `Langlands.NYLL`; the source imports
are replaced by the single focused import of
`Degree.Fields.FiniteAbstractField.Definitions`; the anonymous instance
receives the `PortInternal` name. Universe `u` (source line 30), the section
variable `{G : Type u} [Group G] [TopologicalSpace G]` (source line 46),
binder kinds, attributes, structure fields, docstrings and bodies are otherwise
unchanged, inside `noncomputable section` as in the source.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation or reciprocity assertion.
