import Langlands.Representation.Twist.ContinuousCharacterStatement
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Topology.LocallyConstant.Basic

namespace Langlands

open scoped BigOperators
open Topology

/-- If all nonnegative powers stay within radius one half of 1, the number is 1. -/
theorem complex_eq_one_of_forall_norm_pow_sub_one_lt {z : ℂ}
    (h : ∀ n : ℕ, ‖z ^ n - 1‖ < (1 / 2 : ℝ)) : z = 1 := by
  by_contra hz
  have ha : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have hlarge : 1 < (n : ℝ) * ‖z - 1‖ := (div_lt_iff₀ ha).mp hn
  have hre (i : ℕ) : (1 / 2 : ℝ) ≤ (z ^ i).re := by
    have hi := lt_of_le_of_lt
      (neg_le_abs (z ^ i - 1).re)
      (lt_of_le_of_lt (Complex.abs_re_le_norm _) (h i))
    simp only [Complex.sub_re, Complex.one_re] at hi
    linarith
  have hsum : (n : ℝ) / 2 ≤ (∑ i ∈ Finset.range n, z ^ i).re := by
    calc
      (n : ℝ) / 2 = ∑ _i ∈ Finset.range n, (1 / 2 : ℝ) := by
        simp [div_eq_mul_inv]
      _ ≤ ∑ i ∈ Finset.range n, (z ^ i).re :=
        Finset.sum_le_sum fun i _ => hre i
      _ = (∑ i ∈ Finset.range n, z ^ i).re := by
        simpa only [Complex.reCLM_apply] using
          (map_sum Complex.reCLM (fun i => z ^ i) (Finset.range n)).symm
  have hgeom := congrArg (fun w : ℂ => ‖w‖) (geom_sum_mul z n)
  simp only [norm_mul] at hgeom
  have hbound := mul_le_mul_of_nonneg_right
    (hsum.trans (Complex.re_le_norm _)) ha.le
  rw [hgeom] at hbound
  have hsmall := h n
  nlinarith

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Continuity and an open-subgroup identity basis imply an open character kernel. -/
theorem isOpen_ker_of_continuous_complex_character [NonarchimedeanGroup G]
    (chi : G →* ℂˣ) (hchi : Continuous chi) : IsOpen (chi.ker : Set G) := by
  let O : Set G := {g | ‖(chi g : ℂ) - 1‖ < (1 / 2 : ℝ)}
  have hopen : IsOpen O :=
    isOpen_lt ((Units.continuous_val.comp hchi).sub continuous_const).norm continuous_const
  have hone : (1 : G) ∈ O := by
    simp [O]
  obtain ⟨K, hK⟩ := NonarchimedeanGroup.is_nonarchimedean O (hopen.mem_nhds hone)
  apply chi.ker.isOpen_of_openSubgroup (U := K)
  intro g hg
  change chi g = 1
  apply Units.ext
  change (chi g : ℂ) = 1
  apply complex_eq_one_of_forall_norm_pow_sub_one_lt
  intro n
  have hn := hK (K.pow_mem hg n)
  simpa [O] using hn

/-- The full target with its explicitly quantified nonarchimedean hypothesis. -/
theorem continuousComplexCharacterOpenKernel :
    ContinuousComplexCharacterOpenKernel (G := G) := by
  intro inst chi hchi
  exact isOpen_ker_of_continuous_complex_character chi hchi

end Langlands

namespace Langlands.RankinSelberg

/-- A continuous complex character of a nonarchimedean group is locally constant. -/
theorem isLocallyConstant_of_continuous_complex_character {H : Type*} [Group H]
    [TopologicalSpace H] [NonarchimedeanGroup H] (θ : H →* ℂˣ)
    (hθc : Continuous θ) : IsLocallyConstant (fun u : H => (θ u : ℂ)) := by
  have hθopen : IsOpen (θ.ker : Set H) := isOpen_ker_of_continuous_complex_character θ hθc
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro u
  refine ⟨(fun v : H => u⁻¹ * v) ⁻¹' (θ.ker : Set H),
    hθopen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro v hv
    have hv' : θ (u⁻¹ * v) = 1 := hv
    have he : (θ u)⁻¹ * θ v = 1 := by
      simpa only [map_mul, map_inv] using hv'
    exact congrArg Units.val (inv_mul_eq_one.mp he).symm

end Langlands.RankinSelberg
