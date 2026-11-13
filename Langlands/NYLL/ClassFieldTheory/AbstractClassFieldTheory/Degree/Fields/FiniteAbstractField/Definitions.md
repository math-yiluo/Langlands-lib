# NYLL M010: abstract fields finite over the distinguished base

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
| M010.121 | `FiniteAbstractField` | 1092–1098 | `FiniteAbstractField` |
| M010.123 | `FiniteAbstractField.base` | 1113–1135 | `FiniteAbstractField.base` |
| M010.124 | `FiniteAbstractField.toFiniteAbstractExtension` | 1137–1144 | `FiniteAbstractField.toFiniteAbstractExtension` |
| M010.125 | anonymous `instance` in namespace `FiniteAbstractField` | 1146–1150 | `Langlands.NYLL.PortInternal.M010.d125` |

The section header comment of line 1090 is kept. M010.122
(`eq_of_field_eq`, lines 1102–1111) is a theorem and is published separately as
the Prop-valued target in the paired module `FiniteAbstractField/Statements`.

**`FiniteAbstractField`** (M010.121) keeps the explicit binders
`(G : Type u) [Group G] [TopologicalSpace G]` and exactly the two source fields:
`field : ClosedSubgroup G` and the proof field
`finite : Finite ((baseField G).toSubgroup ⧸ extensionSubgroup (baseField G) field (le_baseField field))`.
So an object is a closed subgroup `G_K ≤ G` together with finiteness of the
quotient of the base-field subgroup `(baseField G).toSubgroup` by `G_K` viewed
as a subgroup of it, i.e. `K` has finite degree over the distinguished base.

**`base`** (M010.123) is `noncomputable def base (G : Type u) [Group G]
[TopologicalSpace G] : FiniteAbstractField G` with `field := baseField G` and the
exact source tactic proof of `finite`: it locally installs normality of the
extension subgroup (rewritten to `⊤` by `ext`/`Iff.rfl`), then proves the
quotient subsingleton by `Quotient.inductionOn₂'` and
`QuotientGroup.eq_iff_div_mem`/`Subgroup.mem_top`, and concludes with
`infer_instance`.

**`toFiniteAbstractExtension`** (M010.124) takes implicit `{G : Type u}` with
its two instances from the section variable and explicit
`(K : FiniteAbstractField G)`, and returns the published
`DegreeData.FiniteAbstractExtension G` with `field := K.field`,
`base := baseField G`, `below := le_baseField K.field`,
`finiteQuotient := K.finite`, exactly as in the source.

**`PortInternal.M010.d125`** (M010.125) is the source anonymous instance
`(K : FiniteAbstractField G) : Finite ((baseField G).toSubgroup ⧸
extensionSubgroup (baseField G) K.field (le_baseField K.field))` with body
`K.finite`. It is declared inside namespace
`Langlands.NYLL.ClassFormation.FiniteAbstractField` with the explicit
`_root_.Langlands.NYLL.PortInternal.M010.d125` name, so its scope, binders and
instance type are those of the source; it is the only instance added, and its
class argument is the quotient by a structure projection of the new type, so it
cannot conflict with Mathlib or Library instances.

Used published declarations (imported by name):
`Langlands.NYLL.ClassFormation.baseField` (M010.003),
`Langlands.NYLL.ClassFormation.le_baseField` (M010.005, module
`Degree.Fields.U005.Proofs`),
`Langlands.NYLL.ClassFormation.DegreeData.FiniteAbstractExtension` (M010.065,
module `Degree.Fields.FiniteExtension.Definitions`) and
`Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002, module
`GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`). The source
writes `extensionSubgroup` under `open CyclicCohomology`; the port keeps the
same `open CyclicCohomology` (now resolving to
`Langlands.NYLL.CyclicCohomology`) and uses the published abbreviation itself,
whose body is `L.toSubgroup.subgroupOf K.toSubgroup`, so the terms are those of
the source.

Modifications by Worker 171: only units M010.121 and M010.123–125 (with the
section header) are extracted; the namespace is prefixed with
`Langlands.NYLL`; the source imports are replaced by the three focused published
imports above; the anonymous instance receives the `PortInternal` name.
Universe `u` (source line 30), the section variable
`{G : Type u} [Group G] [TopologicalSpace G]` (source line 46), `open
CyclicCohomology` (line 24),
binder kinds, structure fields, docstrings, bodies and proof terms are otherwise
unchanged, and the declarations sit in `noncomputable section` as in the source.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit supplies no host class-formation or reciprocity assertion.
