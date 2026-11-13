# NYLL M010: residue data of fields finite over the distinguished base

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
| M010.126 | `ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField` | 1152–1173 | `Langlands.NYLL.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField` |
| M010.127 | `ClassFormation.FiniteAbstractField.residueDegree` | 1175–1179 | `Langlands.NYLL.ClassFormation.FiniteAbstractField.residueDegree` |
| M010.140 | `ClassFormation.FiniteAbstractFieldExtension.toFiniteResidueAbstractExtension` | 1303–1310 | `Langlands.NYLL.ClassFormation.FiniteAbstractFieldExtension.toFiniteResidueAbstractExtension` |

All three declarations take implicit `{G : Type u} [Group G] [TopologicalSpace G]`
from the section variable (source line 46). They sit inside
`noncomputable section` with universe `u` (source line 30) and
`open CyclicCohomology` (source line 24), as in the source.

**`FiniteAbstractField.toFiniteResidueAbstractField`** (M010.126) has the source
attribute `@[implicit_reducible]` and is a `noncomputable def`. Its explicit
arguments are `(K : FiniteAbstractField G)` and `(D : DegreeData G)`, and it
returns a `DegreeData.FiniteResidueAbstractField D`. The field is
`field := K.field`. The field `finiteResidueQuotient`, finiteness of the
residue quotient `D.residueQuotient K.field`, is proved as in the source. By
`Cardinal.lt_aleph0_iff_finite` it suffices that the cardinal
`intersectionIndexCardinal (D.fieldImage K.field) ⊤` is below `ℵ₀`. The image
`D.fieldImage K.field` is rewritten to `K.field.toSubgroup.map D.degree.toMonoidHom`
(`fieldImage_eq_map`). The top subgroup of `ZHatMul` is rewritten to the image of
the distinguished base subgroup; that image is all of `ZHatMul` because the base
is the whole group (`baseField_toSubgroup`) and the degree map is surjective
(`D.degree_surjective`). The cardinal is now the relative residue cardinal of
the finite abstract extension `K.toFiniteAbstractExtension` (M010.124), which is
below `ℵ₀` by M010.081. So the residue quotient of a field of finite degree over
the base is finite: residue finiteness is derived, not assumed.

**`FiniteAbstractField.residueDegree`** (M010.127) is a `noncomputable def`
with explicit `(K : FiniteAbstractField G)` and `(D : DegreeData G)`. It returns
the positive natural `(K.toFiniteResidueAbstractField D).residueDegree : ℕ+`,
the published positive residue degree of a finite-residue field (M010.025).
That degree is `Nat.card (D.residueQuotient K.field)`.

**`FiniteAbstractFieldExtension.toFiniteResidueAbstractExtension`** (M010.140)
is a `noncomputable def` with explicit `(E : FiniteAbstractFieldExtension G)`
and `(D : DegreeData G)`. It returns a `DegreeData.FiniteResidueAbstractExtension D`
with fields `field := E.field.toFiniteResidueAbstractField D`,
`base := E.base.toFiniteResidueAbstractField D`, `below := E.below` and
`finiteQuotient := E.finiteQuotient`. So both endpoints get their finite residue
quotients from M010.126, and the containment and finite relative quotient are
those of `E`. The `finiteQuotient` field of `E` is stated with
`extensionSubgroup` and the target field with `subgroupOf`. These agree because
the published `extensionSubgroup` is an abbreviation with body
`L.toSubgroup.subgroupOf K.toSubgroup`, as in the source.

Used published declarations (imported by name):
`Langlands.NYLL.ClassFormation.FiniteAbstractField` with `toFiniteAbstractExtension`
(M010.121/.124) and `Langlands.NYLL.ClassFormation.FiniteAbstractFieldExtension`
(M010.130), from module `Degree.Fields.FiniteAbstractField.Extension.Definitions`
and the `Degree.Fields.FiniteAbstractField.Definitions` module it imports;
`Langlands.NYLL.ClassFormation.DegreeData.FiniteResidueAbstractField` and its
`residueDegree` (M010.021/.025, module `Degree.Fields.FiniteResidue.Definitions`),
and `Langlands.NYLL.ClassFormation.DegreeData.FiniteResidueAbstractExtension`
(M010.111, module `Degree.Fields.FiniteResidueExtension.Definitions`); the
theorem `Langlands.NYLL.PortInternal.M010.d081` (M010.081, module
`Degree.Fields.FiniteExtension.U081.Proofs`), whose type is the published Prop
`Langlands.NYLL.PortInternal.M010.d081Statement E D :
E.toAbstractExtension.relativeResidueDegreeCardinal D < Cardinal.aleph0`;
`Langlands.NYLL.ClassFormation.DegreeData.fieldImage_eq_map` (M010.011, module
`Degree.Fields.U011.Proofs`); `Langlands.NYLL.ClassFormation.baseField_toSubgroup`
(M010.004, module `Degree.Fields.U004.Proofs`); and, through these imports,
`DegreeData`, `baseField`, `le_baseField`, `fieldImage`, `residueQuotient`,
`ZHatMul`, `DegreeData.AbstractExtension.relativeResidueDegreeCardinal`,
`intersectionIndexCardinal`, `relativeIndexCardinal` and
`Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002).

Modifications by Worker 171: units M010.126, .127 and .140 are extracted into
the module `Degree.Fields.FiniteAbstractField.Residue.Definitions`. They were
held back from the core module `Degree.Fields.FiniteAbstractField.Definitions`
until the M010.081 proof was published. The namespace is prefixed with
`Langlands.NYLL`, and the source imports are replaced by the five focused
published imports above. The source proof of M010.126 ends with
`simpa only [FiniteAbstractField.toFiniteAbstractExtension, DegreeData.AbstractExtension.relativeResidueDegreeCardinal, relativeIndexCardinal] using K.toFiniteAbstractExtension.relativeResidueDegreeCardinal_lt_aleph0 D`.
In this port, the source lemma `relativeResidueDegreeCardinal_lt_aleph0`
(M010.081) is applied under its published name, as
`Langlands.NYLL.PortInternal.M010.d081 K.toFiniteAbstractExtension D`. Its
statement definition `Langlands.NYLL.PortInternal.M010.d081Statement` is added
to the `simpa only` set so that it unfolds to the same proposition as the
source lemma. The proof therefore has the same content as the source proof.
Universe, section variable, binder kinds and names, the attribute, docstrings,
structure fields and the remaining proof steps are unchanged.

The source theorems between these units are not part of this module.
M010.128 `base_residueDegree` is stated as a separate target in
`Degree.Fields.FiniteAbstractField.Residue.Statements`. M010.129
`residueDegree_coe`, an `rfl` lemma in the source, is not ported here.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support unit makes no class-formation or reciprocity claim of its own.
