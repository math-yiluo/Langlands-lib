# NYLL M088.003: evaluation of the intermediate-field unit inclusion

This module proves the published Library proposition
`Langlands.NYLL.LocalClassFieldTheory.intermediateFieldUnitsToGaloisAmbient_applyStatement`
by the theorem
`Langlands.NYLL.LocalClassFieldTheory.intermediateFieldUnitsToGaloisAmbient_apply`.
The theorem's type is exactly that proposition applied to its source
parameters, `intermediateFieldUnitsToGaloisAmbient_applyStatement K Ω E x`.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnits.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has, in this order, explicit `K Ω : Type`, the instances
`[Field K] [Field Ω] [Algebra K Ω]`, an explicit intermediate field
`E : IntermediateField K Ω` and an explicit unit `x : Eˣ`. No Galois,
finite-dimensional or local-field hypothesis is assumed; the published
proposition itself precedes the Galois hypothesis of its section.

Unfolding the published proposition gives

```lean
intermediateFieldUnitsToGaloisAmbient K Ω E (Additive.ofMul x) =
  Additive.ofMul (Units.map E.val.toRingHom x)
```

Here `intermediateFieldUnitsToGaloisAmbient K Ω E` is the published additive
homomorphism `Additive Eˣ →+ Additive Ωˣ` of
`AbsoluteUnitsFixedField.Initial.Definitions`, defined as
`MonoidHom.toAdditive (Units.map E.val.toRingHom)`. The equality says that it
sends `x`, viewed additively, to the image of `x` under the unit map of the
inclusion `E → Ω`, viewed additively.

## Implemented proof

The complete proof term is `rfl`. Both the published proposition and
`intermediateFieldUnitsToGaloisAmbient` unfold definitionally, and
`MonoidHom.toAdditive f (Additive.ofMul x)` reduces to
`Additive.ofMul (f x)`, so the two sides are definitionally equal.

This is the original proof verbatim. The source theorem carries the
attribute `@[simp]`; it is omitted here because the theorem's stated type is
the Prop-valued definition
`intermediateFieldUnitsToGaloisAmbient_applyStatement K Ω E x`, not a visible
equation, so the simplifier would not use it as a rewrite rule. Explicit
rewriting with this theorem still works: the M088.005 proof uses it in `rw`. No auxiliary declaration, extra
hypothesis or instance is introduced. The development check reports only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`, which
enter through the definitions occurring in the statement.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.LocalClassFieldTheory.intermediateFieldUnitsToGaloisAmbient_applyStatement`
  in FixedUnits.Statements (unfolded definitionally).
- The published definition
  `Langlands.NYLL.LocalClassFieldTheory.intermediateFieldUnitsToGaloisAmbient`
  in `AbsoluteUnitsFixedField.Initial.Definitions`, reached through the
  unchanged Statements import chain.
- Mathlib's `MonoidHom.toAdditive`, `Units.map` and `IntermediateField.val`,
  used only by definitional unfolding.

No other proof and no host class-formation or reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean:47–53`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean#L47-L53).
Line 47 is the retained docstring, 48 the omitted `@[simp]`, 49–52 the
signature and 53 the proof `rfl`. The section variables are at line 33,
`(K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]`; the Galois hypothesis of
line 55 comes after this theorem. The
[public partition](../../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m088)
places this proof at M088.003 (source unit lines 49–58) after M088.002.END.
The whole-file SHA-256 is
`392d08ca1431117423181ba326721905cc060686d340ba471b6838f85dd3ebfc`,
recomputed by Worker 96 on 13 November 2026 UTC from the retained snapshot.

| Original in `LocalClassFieldTheory` | Adapted in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- |
| Asserted type of `intermediateFieldUnitsToGaloisAmbient_apply` (M088.003) | Published `intermediateFieldUnitsToGaloisAmbient_applyStatement` in FixedUnits.Statements |
| Proof `intermediateFieldUnitsToGaloisAmbient_apply` | This theorem of the same adapted name in FixedUnits.U003.Proofs |
| `intermediateFieldUnitsToGaloisAmbient` (M088.002) | Existing published definition in AbsoluteUnitsFixedField.Initial.Definitions |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published FixedUnits.Statements import, omits
the unused `open` declarations and the `noncomputable section`, states the
theorem's type as the published proposition applied to `K Ω E x`, and omits
the `@[simp]` attribute.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 96's dated modification
record. Worker 96 extracted this proof directly from the pinned original and
the published statement. No unpublished project draft was reused, and there
are no project coauthors.

The unchanged inherited
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) are retained, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance. Publication under
`lean.proof@1` requires the Lake build, kernel and exact-target checks,
unchanged statement and dependency checks, independent semantic review and
Integrator publication.

This proof covers only M088.003. The fixed-unit criterion M088.004, the range
identification M088.005 and any host class-formation, cup, transfer, Tate or
reciprocity target are separate work.
