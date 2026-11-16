# NYLL M330.005: equality of absolute and relative residue degrees

This module proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.finiteAbstractField_residueDegree_eq_relativeResidueDegreeStatement`
under the adapted source theorem name
`Langlands.NYLL.LocalClassFieldTheory.finiteAbstractField_residueDegree_eq_relativeResidueDegree`.
It imports the existing target from the adjacent
[`ResidueDegreeStatement`](ResidueDegreeStatement.md) module.

The theorem retains the arbitrary universe `u` and the full telescope
`{G : Type u} [Group G] [TopologicalSpace G] (D : DegreeData G)
(H : FiniteAbstractField G)`. Its result is precisely the published target
applied to `D H`, namely
`(H.residueDegree D : ℕ) =
(H.toFiniteAbstractExtension.residueDegree D : ℕ)`.
There are no additional hypotheses or degree constructions.

## Source correspondence

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/AbstractUnramified.lean`,
SHA-256 `095bea2e9d86b74ce22127ea88332ca81fd0433ef86e5e9442bb37363930ca53`.
Source unit M330.005 has its docstring at lines 159–160, theorem telescope
and equality at lines 161–165, and proof at lines 166–188. Its arbitrary
universe is declared at line 123.

The registered source is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The public routing entry is [M330](../../../../../../../../notes/reuse/nyll-public-port/m313-m336.md#m330).

## Implemented proof

The proof uses the actual published quotient definitions. The left degree's
natural value reduces to `Nat.card (D.residueQuotient H.field)`.
The right degree's natural value reduces to the cardinality of the quotient
of `(baseField G).toSubgroup.map D.degree.toMonoidHom` by
`H.field.toSubgroup.map D.degree.toMonoidHom`, viewed as a subgroup of that
base image. This reduction uses the existing
`H.toFiniteAbstractExtension`, whose base is `baseField G`.

Unfolding `DegreeData.residueQuotient` expresses the absolute quotient as
the quotient of the top subgroup of `ZHatMul` by
`(D.fieldImage H.field).subgroupOf ⊤`. The published equality
`D.fieldImage_eq_map` identifies the field image with the subgroup image
under `D.degree.toMonoidHom`. The published `baseField_toSubgroup`
identifies the base subgroup with the top subgroup of `G`. Finally,
`Subgroup.map_top_of_surjective _ D.degree_surjective` identifies its
degree image with the top subgroup of `ZHatMul`. After these rewrites the
two quotient types coincide, so their `Nat.card` values agree by reflexivity.

The upstream proof instead injects natural numbers into `Cardinal`,
uses the equality between finite positive degrees and cardinal residue
degrees, and applies the relative residue-degree multiplication theorem
together with the fact that the distinguished base has residue degree
one (M010.020). The implementation replaces this entire proof route with
the direct quotient identification above. It does not require those
cardinal multiplication and conversion lemmas. Worker 305 supplied the
checked exact-target example on which this implementation is based.

## Modifications and attribution

Worker 317 extracts only M330.005, prefixes the source namespace with
`Langlands.NYLL`, and writes the theorem's result as the already published
Prop-valued target applied to the original explicit parameters. The
original theorem name, docstring, universe and every binder are preserved.
The source's broad imports are replaced by the single published target
import. Only the necessary namespace opening and universe declaration
remain; unrelated source declarations, namespace openings and the
noncomputable section are omitted. The proof is replaced as described
above. The target and all imported constructions remain unchanged.

Upstream uses Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. This proof uses approved
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0 and
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
No change to the proposition is needed for compatibility.

The original Apache-2.0 copyright and author header is retained in the
Lean file. The existing `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
are retained unchanged. No other M330 theorem is included.
