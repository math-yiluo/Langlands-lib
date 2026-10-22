import Langlands.Geometry.Analytic.FiniteBanachAlgebra
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-! # Closed ideals in Noetherian Banach algebras -/

noncomputable section

open scoped BigOperators
open Topology

universe u v

namespace Langlands.Analytic

variable {K : Type u} [NontriviallyNormedField K]
  {A : Type v} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsNoetherianRing A]

include K in
/-- Every ideal in a Noetherian Banach algebra is closed. The proof
constructs a small perturbation of a finite generating family of its
closure and inverts the resulting operator by a geometric series. -/
theorem isClosed_ideal_of_noetherian_banach (I : Ideal A) :
    IsClosed (I : Set A) := by
  classical
  let N := I.topologicalClosure
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := A) (M := N)
  let E := Fin n → A
  let l : E →ₗ[A] N := Fintype.linearCombination A b
  have hl : Function.Surjective l :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination A b).mp hb
  have hlc : Continuous l := by
    change Continuous (fun c : E => ∑ i, c i • b i)
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  let L : E →L[K] N := { l.restrictScalars K with cont := hlc }
  obtain ⟨D, hD, hpre⟩ := L.exists_preimage_norm_le hl
  let ε : ℝ := 1 / (2 * ((n : ℝ) + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have happ : ∀ i : Fin n, ∃ y : N, y.val ∈ I ∧
      ∃ r : E, l r = b i - y ∧ ‖r‖ < ε := by
    intro i
    obtain ⟨y, hy, hdist⟩ :=
      Metric.mem_closure_iff.mp (b i).property (ε / D) (div_pos hε hD)
    let yN : N := ⟨y, I.le_topologicalClosure hy⟩
    obtain ⟨r, hr, hnorm⟩ := hpre (b i - yN)
    refine ⟨yN, hy, r, hr, hnorm.trans_lt ?_⟩
    have hsmall : ‖b i - yN‖ < ε / D := by
      change ‖(b i : A) - y‖ < ε / D
      simpa only [dist_eq_norm] using hdist
    exact (mul_lt_mul_of_pos_left hsmall hD).trans_eq (mul_div_cancel₀ _ hD.ne')
  choose y hy r hr hnorm using happ
  let q : ℝ := ∑ i, ‖r i‖
  have hq : 0 ≤ q := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hq1 : q < 1 := by
    calc
      q ≤ ∑ _i : Fin n, ε := Finset.sum_le_sum fun i _ => (hnorm i).le
      _ = (n : ℝ) * ε := by simp
      _ < 1 := by
        dsimp [ε]
        rw [mul_one_div]
        apply (div_lt_one (by positivity)).mpr
        linarith
  let f : E →ₗ[A] E := Fintype.linearCombination A r
  have hf : ∀ c : E, ‖f c‖ ≤ q * ‖c‖ := by
    intro c
    change ‖∑ i, c i • r i‖ ≤ _
    calc
      ‖∑ i, c i • r i‖ ≤ ∑ i, ‖c i • r i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c‖ * ‖r i‖ := Finset.sum_le_sum fun i _ =>
        (norm_smul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_le_pi_norm c i) (norm_nonneg _))
      _ = q * ‖c‖ := by rw [← Finset.mul_sum, mul_comm]
  let F : E →L[K] E := (f.restrictScalars K).mkContinuous q hf
  have hF : ‖F‖ < 1 := (F.opNorm_le_bound hq hf).trans_lt hq1
  let U : (E →L[K] E)ˣ := Units.oneSub F hF
  have hmem (c : E) : (l ((1 - F) c) : A) ∈ I := by
    have hlf : l (f c) = ∑ i, c i • (b i - y i) := by
      change l (∑ i, c i • r i) = _
      simp only [map_sum, map_smul, hr]
    change (l (c - f c) : A) ∈ I
    rw [map_sub, hlf]
    change (∑ i, c i • b i - ∑ i, c i • (b i - y i) : N).val ∈ I
    rw [← Finset.sum_sub_distrib]
    simp only [smul_sub, sub_sub_cancel]
    change N.subtype (∑ i, c i • y i) ∈ I
    simp only [map_sum, map_smul]
    exact I.sum_mem fun i _ => I.smul_mem (c i) (hy i)
  have hNI : N ≤ I := by
    intro a ha
    obtain ⟨c, hc⟩ := hl ⟨a, ha⟩
    let d : E := (↑U⁻¹ : E →L[K] E) c
    have hd : (1 - F) d = c := by
      have h := congrArg (fun g : E →L[K] E => g c) U.val_inv
      change (↑U : E →L[K] E) ((↑U⁻¹ : E →L[K] E) c) = c at h
      change (1 - F) ((↑U⁻¹ : E →L[K] E) c) = c
      exact h
    have hm := hmem d
    rw [hd, hc] at hm
    exact hm
  have hEq : I.topologicalClosure = I := le_antisymm hNI I.le_topologicalClosure
  exact hEq ▸ I.isClosed_topologicalClosure

end Langlands.Analytic
