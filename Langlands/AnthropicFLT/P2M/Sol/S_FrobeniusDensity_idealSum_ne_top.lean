/-
Ported from `P2M/Sol/S_FrobeniusDensity_idealSum_ne_top.lean` (entire file, 129 lines, including its
solution and auxiliary declarations) of the Anthropic Lean formalization of Fermat's Last Theorem:
registered source `anthropic-flt-complete-lean-source-6e837e75`, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, original file SHA256
91bf5fc1c8b068d3764b3b83571801da2d1acb50428169b6dc9eb4dc39c5ad78.
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
- The import of `P2M.Util` is dropped and its commands are replaced by ordinary Lean commands: 2
  `p2m_open` commands by `open _root_.…`, 1 `p2m_export` command by `export _root_.… (…)`.
- Universes: `universe u v w` is declared; the binder of `K` (originally `Type*`) is `Type u`. The
  audit named these universes `audit_u`, `audit_v`, `audit_w`.

Declaration names and namespaces are unchanged. Apart from the universe generalization, the
mathematical hypotheses and conclusions of the source are retained.
-/
import Langlands.AnthropicFLT.Definitions.Def_FrobeniusDensity_PrimeSums
import Mathlib.NumberTheory.NumberField.DedekindZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w
namespace P2MW.S_FrobeniusDensity_idealSum_ne_top

set_option autoImplicit false

open _root_.Ideal _root_.NumberField _root_.Filter _root_.Topology _root_.Asymptotics _root_.IsDedekindDomain _root_.Ideal.IsDedekindDomain
open scoped ENNReal

namespace FrobeniusDensity
export _root_.FrobeniusDensity (normRpow idealSum idealCount zetaTerm)
open _root_.FrobeniusDensity

variable (K : Type u) [Field K] [NumberField K]

lemma zetaTerm_nonneg (s : ℝ) (n : ℕ) : 0 ≤ zetaTerm K s n := by
  unfold zetaTerm
  split
  · exact le_refl 0
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

private lemma tendsto_sum_idealCount_div :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / n) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  simp only [idealCount]
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOf_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

private lemma isBigO_sum_of_tendsto_div :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ))
      =O[atTop] (fun n => (n : ℝ) ^ (1:ℝ)) := by
  simp only [Real.rpow_one]
  rw [isBigO_iff]

  have hbdd : BddAbove (Set.range (fun n : ℕ =>
      (∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / n)) :=
    (tendsto_sum_idealCount_div K).bddAbove_range
  obtain ⟨C, hC⟩ := hbdd
  refine ⟨max C 0, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [Real.norm_of_nonneg hn'.le,
    Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)]
  calc ∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)
      = ((∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / n) * n := by field_simp
    _ ≤ C * n := mul_le_mul_of_nonneg_right (hC ⟨n, rfl⟩) hn'.le
    _ ≤ max C 0 * n := mul_le_mul_of_nonneg_right (le_max_left _ _) hn'.le

private lemma LSeriesSummable_idealCount {s : ℝ} (hs : 1 < s) :
    LSeriesSummable (fun n => (idealCount K n : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := fun n => (idealCount K n : ℝ))
    ?_ (fun n => Nat.cast_nonneg _) zero_le_one (by simpa using hs)
  exact isBigO_sum_of_tendsto_div K

private lemma term_eq_ofReal_zetaTerm (s : ℝ) (n : ℕ) :
    LSeries.term (fun n => (idealCount K n : ℂ)) s n = (zetaTerm K s n : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [zetaTerm, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, zetaTerm, if_neg hn]
    have hpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_cpow hpos.le,
      Complex.ofReal_neg, Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]

private lemma summable_zetaTerm {s : ℝ} (hs : 1 < s) : Summable (zetaTerm K s) := by
  have h : Summable fun n => ((zetaTerm K s n : ℝ) : ℂ) := by
    refine (LSeriesSummable_idealCount K hs).congr fun n => ?_
    exact term_eq_ofReal_zetaTerm K s n
  exact Complex.summable_ofReal.mp h

private def NormFiber (n : ℕ) : Type _ :=
  {I : {I : Ideal (𝓞 K) // I ≠ ⊥} // Ideal.absNorm I.1 = n}

private noncomputable def normFiberEquiv :
    (Σ n : ℕ, NormFiber K n) ≃ {I : Ideal (𝓞 K) // I ≠ ⊥} where
  toFun p := p.2.1
  invFun I := ⟨Ideal.absNorm I.1, I, rfl⟩
  left_inv p := by rcases p with ⟨n, I, rfl⟩; rfl
  right_inv I := rfl

private lemma tsum_normFiber (s : ℝ) (n : ℕ) :
    ∑' I : NormFiber K n, normRpow K s I.1.1 = ENNReal.ofReal (zetaTerm K s n) := by
  have hconst : ∀ I : NormFiber K n, normRpow K s I.1.1 = (n : ℝ≥0∞) ^ (-s) := fun I => by
    rw [normRpow, I.2]
  rw [tsum_congr hconst, ENNReal.tsum_const]
  rcases eq_or_ne n 0 with rfl | hn
  · have : IsEmpty (NormFiber K 0) := ⟨fun I => I.1.2 (Ideal.absNorm_eq_zero_iff.mp I.2)⟩
    simp [zetaTerm, ENat.card_eq_coe_natCard]
  · have hpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hequiv : NormFiber K n ≃ {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
      { toFun := fun I => ⟨I.1.1, I.2⟩
        invFun := fun I => ⟨⟨I.1, fun h => hn (by rw [← I.2, h, Ideal.absNorm_bot])⟩, I.2⟩
        left_inv := fun I => rfl
        right_inv := fun I => rfl }
    have hfin : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOf_absNorm_eq n).to_subtype
    have hfin' : Finite (NormFiber K n) := Finite.of_equiv _ hequiv.symm
    rw [zetaTerm, if_neg hn, ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_rpow_of_pos hpos, ENat.card_eq_coe_natCard, Nat.card_congr hequiv]
    simp only [ENNReal.ofReal_natCast, idealCount]
    norm_cast

private lemma tsum_equiv' {α β : Type*} (e : α ≃ β) (f : β → ℝ≥0∞) :
    ∑' a, f (e a) = ∑' b, f b := by
  refine le_antisymm (ENNReal.tsum_comp_le_tsum_of_injective e.injective f) ?_
  simpa using ENNReal.tsum_comp_le_tsum_of_injective e.symm.injective fun a => f (e a)

private lemma idealSum_eq_tsum_zetaTerm (s : ℝ) :
    idealSum K s = ∑' n : ℕ, ENNReal.ofReal (zetaTerm K s n) := by
  rw [idealSum, ← tsum_equiv' (normFiberEquiv K) (fun I => normRpow K s I.1),
    ENNReal.tsum_sigma']
  exact tsum_congr fun n => tsum_normFiber K s n

end FrobeniusDensity

theorem solution (K : Type u) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    FrobeniusDensity.idealSum K s ≠ ⊤ := by
  rw [FrobeniusDensity.idealSum_eq_tsum_zetaTerm,
    ← ENNReal.ofReal_tsum_of_nonneg (FrobeniusDensity.zetaTerm_nonneg K s)
      (FrobeniusDensity.summable_zetaTerm K hs)]
  exact ENNReal.ofReal_ne_top
