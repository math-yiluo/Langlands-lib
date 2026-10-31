# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop`

Ported for task `ab019f66-cba5-4921-aa53-b9cfb52e5456` (descent of geometric connectedness to finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text. The FLT `attribute [-…]`
  lines after the namespace header (which locally deactivate instances and simp lemmas declared in
  imported FLT modules) are kept unchanged.

## Content

Proof (namespace `SolZ1`, inside a `noncomputable section`). Write `𝔪` for the maximal ideal of `A`
and `P_k = P ×_A Spec (A ⧸ 𝔪^k)` with `j_k : P_k ⟶ P`; for `k ≠ 0` the image of `j_k` is the
closed fibre `q⁻¹{closedPoint}` (`range_jk`). Suppose the closed fibre is covered by disjoint open
sets `u`, `v` both meeting it. Take `c` from `exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper`
(with `I = 𝔪`, `n = 1`). On `P_{1+c}` the preimages of `u` and `v` form a disjoint open cover, so
there is an idempotent global section `e` equal to `1` on one and `0` on the other
(`exists_section_eq_one_eq_zero`), with `D(e)` the preimage of `u` (`basicOpen_eq_of_res`). Its
restriction to `P_1` comes from a global section `a = q.appTop b` of `P` (`q.appTop` is
bijective), so `D(a|_{P_1})` is the preimage of `u`. If `b` is a unit this preimage is everything,
contradicting that `v` meets the fibre; otherwise `b ∈ 𝔪` restricts to `0` on `P_1`, so the preimage
of `u` is empty, contradicting that `u` meets the fibre (`main`). `solution` applies `main`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- lemma `P2MW.S_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop.SolZ1.exists_section_eq_one_eq_zero`
- abbrev `P2MW.S_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop.SolZ1.ιk`
- abbrev `P2MW.S_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop.SolZ1.Pk`
- abbrev `P2MW.S_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop.SolZ1.jk`
- lemma `P2MW.S_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop.SolZ1.range_ιk`
- lemma `P2MW.S_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop.SolZ1.range_jk`
- lemma `P2MW.S_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop.SolZ1.basicOpen_eq_of_res`
- theorem `P2MW.S_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop.SolZ1.main`
- theorem `P2MW.S_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper` (same contribution).
All modules also import `Mathlib`.
