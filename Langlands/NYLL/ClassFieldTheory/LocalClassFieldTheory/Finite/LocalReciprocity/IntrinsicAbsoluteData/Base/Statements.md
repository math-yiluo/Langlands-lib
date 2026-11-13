# The finite intrinsic base is the distinguished finite base: statement

This module defines the closed proposition
`Langlands.NYLL.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_baseStatement`,
the statement phase of source row M091.007. It packages the complete source
theorem signature as a `def` returning `Prop` and supplies no proof. A later
proof child will prove it under the name
`Langlands.NYLL.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base`.

## Parameters

The proposition universally quantifies, in the source order,

```lean
(F : Type) [Field F]
```

The field `F` lies in `Type` (universe zero), as in the source. There is no
other hypothesis.

## Conclusion

```lean
intrinsicFiniteAbstractBase F =
  Langlands.NYLL.ClassFormation.FiniteAbstractField.base
    (intrinsicAbsoluteGalois F)
```

Both sides are terms of
`Langlands.NYLL.ClassFormation.FiniteAbstractField (intrinsicAbsoluteGalois F)`,
where `intrinsicAbsoluteGalois F` is `Gal(SeparableClosure F / F)` with its
Krull topology. A `FiniteAbstractField G` is a closed subgroup `field` of `G`
together with a proof `finite` that the quotient of the distinguished base
field `baseField G` (the closed subgroup `⊤`) by the extension subgroup of
`field` is finite.

- The left side, `intrinsicFiniteAbstractBase F` (M091.006), has `field` equal
  to `intrinsicAbstractBase F`, the closed fixing subgroup of the bottom
  intermediate field `⊥` of `SeparableClosure F` over `F`.
- The right side, `FiniteAbstractField.base (intrinsicAbsoluteGalois F)`
  (M010.123), has `field` equal to `baseField (intrinsicAbsoluteGalois F)`.

The two `field` components are equal closed subgroups, but not by
definition. The `finite` components are proofs, so the statement says that
the intrinsic base, viewed as a finite abstract field, is the distinguished
finite base of the abstract class formation.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M091.001, `LocalClassFieldTheory.intrinsicAbsoluteGalois` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbsoluteGalois` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions`) |
| M091.006, `LocalClassFieldTheory.intrinsicFiniteAbstractBase` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicFiniteAbstractBase` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Base.Definitions`) |
| M010.121, `ClassFormation.FiniteAbstractField` | `Langlands.NYLL.ClassFormation.FiniteAbstractField` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions`) |
| M010.123, `ClassFormation.FiniteAbstractField.base` | `Langlands.NYLL.ClassFormation.FiniteAbstractField.base` (same module) |

The module imports only the Library module of `intrinsicFiniteAbstractBase`,
which imports the modules of the other three declarations.

## Relation to other Library and Mathlib declarations

No published declaration states this equality. A search of the Library
`.lean` files (commit `430cc03fe803c5dbf74bc3baf91e8f7a2c26ea9c`) found
`intrinsicFiniteAbstractBase` only in its defining module, and no file states
an equality with `FiniteAbstractField.base` as one side. Related published
declarations are:

- `Langlands.NYLL.LocalClassFieldTheory.closedFixingSubgroup_bot_eq_baseField`
  (M089.001, proved in
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.U001.Proofs`),
  the equality of the underlying closed subgroups
  `closedFixingSubgroup F (SeparableClosure F) ⊥ = baseField _`. This
  statement lifts it to the bundled finite abstract fields.
- `Langlands.NYLL.ClassFormation.FiniteAbstractField.eq_of_field_eqStatement`
  (M010.122), the closed proposition that two finite abstract fields with
  equal `field` components are equal. The source proof of M091.007 combines it
  with M089.001.

Mathlib has no notion of `FiniteAbstractField`.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/IntrinsicAbsoluteData.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/IntrinsicAbsoluteData.lean>).
The complete file was read and its SHA-256 verified as
`307ae64486245113f5aa94505bbc184048f4daec1af85f89f94f965c57b25e5a`.
The docstring, the `@[simp]` attribute and the signature occupy lines 77–83;
the proof occupies lines 84–87 after `:= by` on line 83. The header occupies
lines 1–5, the `noncomputable section` line 20, the namespace line 22 and the
`open` lines 24–25.

| Source unit and original declaration | Adapted declaration and phase |
| --- | --- |
| M091.007, `LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_baseStatement`, closed Prop target |
| Same source theorem, later proof phase | `Langlands.NYLL.LocalClassFieldTheory.intrinsicFiniteAbstractBase_eq_base`, reserved for the proof child |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes to the source theorem:

- The theorem becomes a Prop-valued definition with the `Statement` suffix.
  Its explicit parameter `F` and instance `[Field F]` become universal
  binders in the same order, and the proof is omitted for the separate proof
  phase.
- The source `@[simp]` attribute is dropped, because a `def` returning `Prop`
  is not a simp lemma. The proof child may restore it on the proved theorem.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`, and
  `FiniteAbstractField.base` is written fully qualified as
  `Langlands.NYLL.ClassFormation.FiniteAbstractField.base` instead of being
  reached through the source `open ClassFormation`.
- The source imports `Mathlib.FieldTheory.IsSepClosed` and the module
  `GaloisExtensionQuotient`. The port imports only the Library module
  `IntrinsicAbsoluteData.Base.Definitions`.
- The `noncomputable section` and the `open` lines are omitted. The statement
  lives in its own file `IntrinsicAbsoluteData/Base/Statements`, next to the
  definition it is about. All other declarations of the source file are
  omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance, and the Apache-2.0 notice.
It also records these modifications. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only the M091.007 statement target. Its proof is not part
of this unit.
