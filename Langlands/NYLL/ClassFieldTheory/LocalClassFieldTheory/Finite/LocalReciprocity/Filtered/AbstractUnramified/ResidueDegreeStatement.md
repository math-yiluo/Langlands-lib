# NYLL M330.005: absolute and relative residue-degree target

This module records the exact proposition that the absolute residue degree
of an abstract field finite over the distinguished base equals its relative
residue degree over that base. It publishes a statement target; the proof is
separate.

The source is Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/AbstractUnramified.lean`
(file SHA-256
`095bea2e9d86b74ce22127ea88332ca81fd0433ef86e5e9442bb37363930ca53`).
It is available in the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The registered attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement` has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Exact source correspondence

Source unit M330.005 is
`LocalClassFieldTheory.finiteAbstractField_residueDegree_eq_relativeResidueDegree`.
Its docstring is at lines 159–160, its telescope and conclusion at
lines 161–165, and its proof at lines 166–188. The source declares
`universe u` at line 123.

The adapted declaration is
`Langlands.NYLL.LocalClassFieldTheory.finiteAbstractField_residueDegree_eq_relativeResidueDegreeStatement`.
Its full telescope and body, with the published types written in full, are:

```lean
{G : Type u} [Group G] [TopologicalSpace G]
(D : Langlands.NYLL.ClassFormation.DegreeData G)
(H : Langlands.NYLL.ClassFormation.FiniteAbstractField G) : Prop :=
  (H.residueDegree D : ℕ) =
    (H.toFiniteAbstractExtension.residueDegree D : ℕ)
```

The universe `u` remains arbitrary. The group, its group instance and its
topology remain implicit; `D` and then `H` remain explicit. The source has
no topological-group, local-field, Galois, normality or unramifiedness
hypothesis, and none is added. Both sides are coerced from positive natural
numbers to natural numbers exactly as in the source.

## Published constructions reused

The left side uses
`Langlands.NYLL.ClassFormation.FiniteAbstractField.residueDegree`
(M010.127), imported from
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Residue.Definitions`.
It is the positive degree of `H.toFiniteResidueAbstractField D`, whose
natural value is the cardinality of the actual absolute residue quotient.
Its finite-residue package is the published M010.126 construction.

The right side uses
`Langlands.NYLL.ClassFormation.FiniteAbstractField.toFiniteAbstractExtension`
(M010.124) and
`Langlands.NYLL.ClassFormation.DegreeData.FiniteAbstractExtension.residueDegree`
(M010.086). The latter is imported from
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.NumericDefinitions`.
The extension has field `H.field` and base
`Langlands.NYLL.ClassFormation.baseField G`. Its positive relative residue
degree is the cardinality of the quotient of the base subgroup's image
under `D.degree` by the field subgroup's image, restricted to that base
image. Thus the target compares the published absolute degree with the
published relative degree for the extension over the distinguished base.
No data construction is copied, redefined or taken as an extra parameter.

## Modifications and attribution

Worker 317 extracted only the statement of M330.005, added the
`Langlands.NYLL` namespace prefix and `Statement` suffix, and changed the
source `theorem` with a proof into a `def` returning `Prop` whose body is
the original conclusion. The original docstring is retained. The source
proof at lines 166–188 is omitted. The source's broad imports are replaced
by the two focused published imports listed above. Only the necessary
`ClassFormation` namespace opening and the arbitrary universe declaration
are retained; the source's unrelated openings, noncomputable section and
other declarations are omitted. No mathematical binder, hypothesis,
coercion or equality is changed.

The source targets Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; this isolated target uses the
approved project environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`,
Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. No compatibility change to
the proposition is needed.

The original copyright and author header is retained in the Lean file.
The existing `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
are retained unchanged. This module and this section record the
modifications. No other M330 unit or reciprocity theorem is included.
