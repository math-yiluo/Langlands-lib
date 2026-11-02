# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_CurveModel_nonempty_of_perfectField`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicCurve_CurveModel_nonempty_of_perfectField.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicCurve_CurveModel_nonempty_of_perfectField.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicCurve_CurveModel_nonempty_of_perfectField`. Statement. `AlgebraicCurve.CurveModel.nonempty_of_perfectField`: let `K` be an infinite perfect field (universe
`u`) and `L / K` a field extension (any universe) with an element `x` transcendental over `K` such
that `L` is finite over `K(x)`. Then `L / K` has a curve model (`Nonempty (CurveModel K L)`).

Proof (namespace `P2mModelK`). `nonempty_of_separatingGenerator`: for a separating transcendental
`t` (with `L` separable over `K(t)`), the ported theorem
`CurveModel.isProper_smooth_places_affineCover_glued` packages `glued K t` as a `CurveModel K L`.
`nonempty_same_universe`: if `L` is in the universe of `K`, `L` is essentially of finite type
(`essFiniteType_of_hfg`), `{x}` is a transcendence basis (`isTranscendenceBasis_of_hfg`), so over
the perfect field `K` there is a separating transcendence basis of cardinality `1`
(`exists_isTranscendenceBasis_and_isSeparable_of_perfectField`), giving a separating generator.
`main`: in general `L` is small (`small_of_hfg`), so apply the previous case to `Shrink L` and
transport the model along the isomorphism (`congr`, `transcendental_algEquiv`,
`finiteDimensional_algEquiv`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicCurve_CurveModel_nonempty_of_perfectField.P2mModelK.nonempty_of_separatingGenerator`
- theorem `P2MW.S_AlgebraicCurve_CurveModel_nonempty_of_perfectField.P2mModelK.essFiniteType_of_hfg`
- theorem `P2MW.S_AlgebraicCurve_CurveModel_nonempty_of_perfectField.P2mModelK.isTranscendenceBasis_of_hfg`
- theorem `P2MW.S_AlgebraicCurve_CurveModel_nonempty_of_perfectField.P2mModelK.nonempty_same_universe`
- def `P2MW.S_AlgebraicCurve_CurveModel_nonempty_of_perfectField.P2mModelK.congr`
- theorem `P2MW.S_AlgebraicCurve_CurveModel_nonempty_of_perfectField.P2mModelK.small_of_hfg`
- theorem `P2MW.S_AlgebraicCurve_CurveModel_nonempty_of_perfectField.P2mModelK.transcendental_algEquiv`
- theorem `P2MW.S_AlgebraicCurve_CurveModel_nonempty_of_perfectField.P2mModelK.finiteDimensional_algEquiv`
- theorem `P2MW.S_AlgebraicCurve_CurveModel_nonempty_of_perfectField.P2mModelK.main`
- theorem `P2MW.S_AlgebraicCurve_CurveModel_nonempty_of_perfectField.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModelConstruction` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaces` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued` (same contribution).
Other imports: `Mathlib`.
