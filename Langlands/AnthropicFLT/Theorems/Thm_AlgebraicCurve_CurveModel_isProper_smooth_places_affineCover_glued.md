# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.solution K t ht`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicCurve.CurveModel.isProper_smooth_places_affineCover_glued`: let `K` be an infinite perfect
field, `L / K` a field extension and `t ∈ L` nonzero and transcendental over `K` with `L` finite and
separable over `K(t)`. Then for the glued scheme `glued K t` of `Def_AlgebraicCurve_CurveModelConstruction`
(two affine charts given by the integral closures of `K[t]` and `K[t⁻¹]` in `L`), the structure
morphism `gluedToBase K t` to `Spec K` is proper and smooth of relative dimension `1`; there is a
bijection `P` from the closed points to the places of `L / K` such that the image in `L` of the stalk
at each closed point `x` is the valuation ring of `P x`; and every finite set of points lies in an
affine open.

The proof term applies the companion solution theorem `P2MW.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicCurve.CurveModel.isProper_smooth_places_affineCover_glued`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModelConstruction` (same contribution), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued` (same contribution).
Other imports: none.
