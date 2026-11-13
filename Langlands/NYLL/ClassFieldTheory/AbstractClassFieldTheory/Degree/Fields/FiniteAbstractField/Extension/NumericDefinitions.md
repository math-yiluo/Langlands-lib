# NYLL M010: positive relative residue degree of a finite field extension

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
| M010.136 | `ClassFormation.FiniteAbstractFieldExtension.residueDegree` | 1278–1281 | `Langlands.NYLL.ClassFormation.FiniteAbstractFieldExtension.residueDegree` |

The declaration takes implicit `{G : Type u} [Group G] [TopologicalSpace G]`
from the section variable (source line 46). It sits inside
`noncomputable section` with universe `u` (source line 30), as in the source.

**`FiniteAbstractFieldExtension.residueDegree`** (M010.136) is a
`noncomputable def` with explicit `(E : FiniteAbstractFieldExtension G)` and
then explicit `(D : DegreeData G)`. It returns a positive natural number
`ℕ+`. Its body is the source body
`E.toFiniteAbstractExtension.residueDegree D`. So it forgets the field
structure of the extension `E` (M010.132 `toFiniteAbstractExtension`) and
takes the positive relative residue degree of the underlying finite abstract
extension (M010.086). The underlying extension has top field
`E.field.field` and base `E.base.field`. Write `B` for the image of
`E.base.field.toSubgroup` and `F` for the image of
`E.field.field.toSubgroup` under `D.degree.toMonoidHom`. The degree is the
`Nat.card` of the coset type `↥B ⧸ F.subgroupOf B`. It is positive because that coset type is nonempty and finite; the
finiteness is derived in M010.083 from the cardinal fundamental identity, not
assumed.

Used published declarations (imported by name):
`Langlands.NYLL.ClassFormation.FiniteAbstractFieldExtension` (M010.130) and
its `toFiniteAbstractExtension` (M010.132), from module
`Degree.Fields.FiniteAbstractField.Extension.Definitions`;
`Langlands.NYLL.ClassFormation.DegreeData.FiniteAbstractExtension.residueDegree`
(M010.086) and the instance
`Langlands.NYLL.ClassFormation.DegreeData.FiniteAbstractExtension.residueQuotientFinite`
(M010.083) used by it, from module
`Degree.Fields.FiniteExtension.NumericDefinitions`; and, through these
imports, `Langlands.NYLL.ClassFormation.DegreeData`. Module names here are
abbreviated; each full name has the prefix
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.`.

Modifications by Worker 171: unit M010.136 is extracted into the module
`Degree.Fields.FiniteAbstractField.Extension.NumericDefinitions`. It was held
back from `Degree.Fields.FiniteAbstractField.Extension.Definitions` until
M010.086 was published. The namespace is prefixed with `Langlands.NYLL`, and
the source imports are replaced by the two focused published imports above.
Universe, section variable, binder kinds and names, docstring and body are
unchanged.

The source declarations around this unit are not part of this module.
M010.135 `degree` is in `Degree.Fields.FiniteAbstractField.Extension.Definitions`.
M010.137 `ramificationIndex` is not ported here. M010.138
`residueDegree_eq_degree_of_isUnramified` is stated as a separate target in
`Degree.Fields.FiniteAbstractField.Extension.NumericStatements`.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit makes no class-formation or reciprocity claim of its own.
