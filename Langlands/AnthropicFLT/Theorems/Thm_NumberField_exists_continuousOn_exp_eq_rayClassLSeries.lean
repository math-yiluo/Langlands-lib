/-
Ported from `Theorems/Thm_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean` (entire file,
25 lines) of the Anthropic Lean formalization of Fermat's Last Theorem: registered source
`anthropic-flt-complete-lean-source-6e837e75`, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
original file SHA256 fd0fd915e8695c3a0cc22e4b770a7772594400fea066cf3c8959aa6f5234fd0c.
Copyright 2026 Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.

Complete list of edits to the source text (the paired Markdown file gives the same list; the audit
`notes/reuse/anthropic-chebotarev-audit.md` and its evidence files `compatibility.md`,
`universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact
diffs):
- Imports of FLT modules use the `Langlands.AnthropicFLT` prefix.
- The source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set
  after the imports.
- The audit's modification comments are replaced by the port header.
- The import of `P2M.Util` is dropped.
- Universes: `universe u v w` is declared; the binder of `K` (originally `Type`) is `Type u`. The
  audit named these universes `audit_u`, `audit_v`, `audit_w`.
- Cleanup: the line `attribute [-instance] FrobeniusDensity.liesOver_ratBelow
  FrobeniusDensity.isMaximal_ratPrimeIdeal` was removed; the line `attribute [-simp]
  TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec` was removed; the proof `by
  p2m_exact_reverting
  @_root_.P2MW.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.solution` was replaced by
  `apply @_root_.P2MW.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.solution <;>
  assumption`.

Declaration names and namespaces are unchanged. Apart from the universe generalization, the
mathematical hypotheses and conclusions of the source are retained.
-/
import Langlands.MathlibBase
import Langlands.AnthropicFLT.Definitions.Def_NumberField_CompletedRayL
import Langlands.AnthropicFLT.Definitions.Def_NumberField_RayCharacterData
import Langlands.AnthropicFLT.P2M.Sol.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply
open scoped nonZeroDivisors

theorem NumberField.exists_continuousOn_exp_eq_rayClassLSeries
    (K : Type u) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) :
    ∃ Λ : ℝ → ℂ, ContinuousOn Λ (Set.Ioi 1) ∧
      (∀ s : ℝ, 1 < s → Complex.exp (Λ s) = M4aTorus.rayClassLSeries K 𝔣 χ s) ∧
      (∀ s : ℝ, 1 < s → Summable fun v : HeightOneSpectrum (𝓞 K) =>
          M4aP2.chiIdeal K 𝔣 χ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) *
            (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))) ∧
      ∃ C : ℝ, ∀ s : ℝ, 1 < s →
        ‖Λ s - ∑' v : HeightOneSpectrum (𝓞 K),
            M4aP2.chiIdeal K 𝔣 χ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))‖ ≤ C := by
  apply @_root_.P2MW.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.solution <;> assumption
