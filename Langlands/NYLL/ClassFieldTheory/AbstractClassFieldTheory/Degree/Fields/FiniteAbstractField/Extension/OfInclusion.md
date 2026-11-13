# NYLL M010: bundling a finite inclusion over a finite field

The source is Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`
(file SHA-256 `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`).
Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Original name | Source lines | Adapted name |
| --- | --- | --- | --- |
| M010.131 | `ClassFormation.FiniteAbstractFieldExtension.ofInclusion` | 1218–1253 | `Langlands.NYLL.ClassFormation.FiniteAbstractFieldExtension.ofInclusion` |

**`FiniteAbstractFieldExtension.ofInclusion`** (M010.131) has the source
attribute `@[implicit_reducible]` and is a `noncomputable def`. It takes
implicit `{G : Type u} [Group G] [TopologicalSpace G]` from the section
variable (source line 46). Then come, in source order, the explicit
`(field : ClosedSubgroup G)`, `(base : FiniteAbstractField G)` and
`(below : field.toSubgroup ≤ base.field.toSubgroup)`, and the named
instance-implicit binder
`[finiteQuotient : Finite (base.field.toSubgroup ⧸ extensionSubgroup base.field field below)]`.
It returns a `FiniteAbstractFieldExtension G` with these fields:

- `field` is the `FiniteAbstractField G` with underlying closed subgroup
  `field`. Its finiteness proof over the distinguished base is the source
  proof. The tower `field ≤ base.field ≤ baseField G`, a
  `DegreeData.AbstractExtension.Tower G`, has total degree cardinal equal to
  the product of the two step degree cardinals (`T.degreeCardinal_mul`). The
  first factor is the cardinal of the finite quotient `finiteQuotient`. The
  second is the cardinal of the finite quotient of `base` over the
  distinguished base, an instance by `PortInternal.M010.d125`. Both are below
  `ℵ₀`, so their product is too (`Cardinal.mul_lt_aleph0`), and
  `Cardinal.lt_aleph0_iff_finite` turns this into the `Finite` field.
- `base := base`, `below := below`, `finiteQuotient := finiteQuotient`.

So the upper endpoint is not assumed to be finite over the distinguished base.
Its finiteness is derived from the actual quotient tower, as in the source.

Used published declarations (imported by name):
`Langlands.NYLL.ClassFormation.FiniteAbstractFieldExtension` and its instance
`Langlands.NYLL.PortInternal.M010.d139` (M010.130/.139, module
`Degree.Fields.FiniteAbstractField.Extension.Definitions`), which brings in
`Langlands.NYLL.ClassFormation.FiniteAbstractField` and the instance
`Langlands.NYLL.PortInternal.M010.d125` (M010.121/.125);
`Langlands.NYLL.ClassFormation.DegreeData.AbstractExtension.Tower` with its
`totalExtension`, `topExtension`, `baseExtension` and the `degreeCardinal` of
an abstract extension (module `Degree.Fields.AbstractExtension.StructuralDefinitions`
and `Degree.Fields.AbstractExtension.Definitions`); the theorem
`Langlands.NYLL.ClassFormation.DegreeData.AbstractExtension.Tower.degreeCardinal_mul`
(M010.041, module `Degree.Fields.AbstractExtension.U041.Proofs`), whose type is
the published Prop
`Tower.degreeCardinal_mulStatement T : T.topExtension.degreeCardinal * T.baseExtension.degreeCardinal = T.totalExtension.degreeCardinal`;
`Langlands.NYLL.ClassFormation.baseField` (module `Degree.Fields.Definitions`)
and the theorem `Langlands.NYLL.ClassFormation.le_baseField` (module
`Degree.Fields.U005.Proofs`), both reached through the imports above; and
`Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002). As in the
source, `extensionSubgroup` is written under `open CyclicCohomology` (source
line 24), now resolving to the published abbreviation with body
`L.toSubgroup.subgroupOf K.toSubgroup`. The `rw [← T.degreeCardinal_mul]` step
of the source compiles unchanged against the published Prop-valued statement
type, so the construction is the source one.

Modifications by Worker 171: only unit M010.131 is extracted, into its own
module `Degree.Fields.FiniteAbstractField.Extension.OfInclusion`. The rest of
the namespace is in `Degree.Fields.FiniteAbstractField.Extension.Definitions`,
and `ofInclusion` was published later because it needs the M010.041 proof.
The namespace is prefixed with `Langlands.NYLL`. The source imports are
replaced by the two focused published imports above. Universe `u` (source
line 30), the section variable, binder kinds and names, the attribute, the
docstring, the structure fields and the complete proof term are otherwise
unchanged, inside `noncomputable section` as in the source.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit makes no class-formation or reciprocity claim of its own.
