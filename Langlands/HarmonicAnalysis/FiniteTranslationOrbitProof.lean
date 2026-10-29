import Langlands.HarmonicAnalysis.FiniteTranslationOrbitStatement
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Proof of uniform recurrences and compact-set growth along translation orbits

This module proves `Langlands.HarmonicAnalysis.FiniteTranslationOrbitStatement`.
The recurrence comes from the Cayley--Hamilton theorem for left translation by
`t` on the finite-dimensional span of left translates. The growth bound
follows from an elementary estimate for solutions of a linear recurrence,
applied to the recurrences for `t` and for `t⁻¹`, with initial values bounded
on the compact set by continuity.
-/

namespace Langlands.HarmonicAnalysis

open Polynomial

universe uG

/-- Cayley--Hamilton for left translation by `s` on the span of left
translates gives one recurrence for every orbit sequence `n ↦ η (s ^ n * x)`. -/
private theorem exists_orbit_recurrence {G : Type*} [Group G] (η : G → ℂ)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun b : G => fun a : G => η (b * a)))) (s : G) :
    ∃ E : LinearRecurrence ℂ, ∀ x : G,
      E.IsSolution (fun n : ℕ => η (s ^ n * x)) := by
  let V : Submodule ℂ (G → ℂ) :=
    Submodule.span ℂ (Set.range fun b : G => fun a : G => η (b * a))
  have : FiniteDimensional ℂ V := hfin
  let T : (G → ℂ) →ₗ[ℂ] (G → ℂ) := LinearMap.funLeft ℂ ℂ (fun a : G => s * a)
  have hVT : V ≤ V.comap T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    refine Submodule.subset_span ⟨b * s, ?_⟩
    funext a
    simp [T, LinearMap.funLeft_apply, mul_assoc]
  let Tv : Module.End ℂ V := T.restrict fun f hf => hVT hf
  have hpow : ∀ (m : ℕ) (w : V) (x : G),
      ((Tv ^ m) w : G → ℂ) x = (w : G → ℂ) (s ^ m * x) := by
    intro m
    induction m with
    | zero => intro w x; simp
    | succ m ih =>
      intro w x
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ', mul_assoc]
      rfl
  have hηV : (fun a : G => η a) ∈ V :=
    Submodule.subset_span ⟨1, by funext a; simp⟩
  let w : V := ⟨fun a : G => η a, hηV⟩
  have hw : (w : G → ℂ) = fun a : G => η a := rfl
  let p : ℂ[X] := Tv.charpoly
  have hmonic : p.Monic := Tv.charpoly_monic
  have hCH : aeval Tv p = 0 := Tv.aeval_self_charpoly
  rw [aeval_eq_sum_range, Finset.sum_range_succ, hmonic.coeff_natDegree, one_smul] at hCH
  refine ⟨⟨p.natDegree, fun i => -p.coeff i⟩, fun x n => ?_⟩
  have key := congrArg (fun A : Module.End ℂ V => ((A ((Tv ^ n) w) : V) : G → ℂ) x) hCH
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, Pi.add_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, LinearMap.zero_apply,
    Submodule.coe_zero, Pi.zero_apply] at key
  simp only [hpow, hw, ← mul_assoc, ← pow_add] at key
  show η (s ^ (n + p.natDegree) * x) =
    ∑ i : Fin p.natDegree, -p.coeff i * η (s ^ (n + i) * x)
  rw [Fin.sum_univ_eq_sum_range (fun i => -p.coeff i * η (s ^ (n + i) * x))]
  simp only [neg_mul, Finset.sum_neg_distrib]
  linear_combination key

/-- A solution of a linear recurrence whose first `E.order` values are bounded
by `C` grows at most like `C * B ^ n` once `B ≥ 1` dominates the sum of the
coefficient norms. -/
private theorem norm_le_of_isSolution (E : LinearRecurrence ℂ) {u : ℕ → ℂ}
    (hu : E.IsSolution u) {B C : ℝ} (hB : 1 ≤ B) (hcB : ∑ i, ‖E.coeffs i‖ ≤ B)
    (hC : 0 ≤ C) (hinit : ∀ i < E.order, ‖u i‖ ≤ C) :
    ∀ n : ℕ, ‖u n‖ ≤ C * B ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hn : n < E.order
  · calc ‖u n‖ ≤ C := hinit n hn
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * B ^ n := mul_le_mul_of_nonneg_left (one_le_pow₀ hB) hC
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (not_lt.1 hn)
    have hBpos : 0 < B := by linarith
    have hterm : ∀ i : Fin E.order,
        ‖E.coeffs i * u (m + i)‖ ≤ ‖E.coeffs i‖ * (C * B ^ (m + i)) := by
      intro i
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (ih _ (by have := i.isLt; omega)) (norm_nonneg _)
    have hpowle : ∀ i : Fin E.order,
        B * (C * B ^ (m + i)) ≤ C * B ^ (m + E.order) := by
      intro i
      calc B * (C * B ^ (m + i)) = C * B ^ (m + i + 1) := by ring
        _ ≤ C * B ^ (m + E.order) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hB (by have := i.isLt; omega)) hC
    have hsum : B * ∑ i, ‖E.coeffs i‖ * (C * B ^ (m + i)) ≤
        B * (C * B ^ (m + E.order)) := by
      calc B * ∑ i, ‖E.coeffs i‖ * (C * B ^ (m + i))
          = ∑ i, ‖E.coeffs i‖ * (B * (C * B ^ (m + i))) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ ≤ ∑ i, ‖E.coeffs i‖ * (C * B ^ (m + E.order)) :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hpowle i) (norm_nonneg _)
        _ = (∑ i, ‖E.coeffs i‖) * (C * B ^ (m + E.order)) := by
          rw [Finset.sum_mul]
        _ ≤ B * (C * B ^ (m + E.order)) :=
          mul_le_mul_of_nonneg_right hcB (mul_nonneg hC (pow_nonneg hBpos.le _))
    rw [hu m]
    calc ‖∑ i, E.coeffs i * u (m + i)‖ ≤ ∑ i, ‖E.coeffs i * u (m + i)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i, ‖E.coeffs i‖ * (C * B ^ (m + i)) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ ≤ C * B ^ (m + E.order) := le_of_mul_le_mul_left hsum hBpos

/-- Finitely many initial orbit values `η (s ^ i * u)`, `i < D`, are bounded
uniformly for `u` in a compact set. -/
private theorem exists_orbit_initial_bound {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {η : G → ℂ} (hη : Continuous η) (s : G) (D : ℕ)
    {K : Set G} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i < D, ∀ u ∈ K, ‖η (s ^ i * u)‖ ≤ C := by
  have hK' : IsCompact (⋃ i ∈ Finset.range D, (fun u : G => s ^ i * u) '' K) :=
    (Finset.range D).isCompact_biUnion fun i _ => hK.image (continuous_const.mul continuous_id)
  obtain ⟨C, hC⟩ := hK'.exists_bound_of_continuousOn hη.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun i hi u hu => (hC _ ?_).trans (le_max_left _ _)⟩
  exact Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hi, Set.mem_image_of_mem _ hu⟩

/-- Proof of `FiniteTranslationOrbitStatement`: one recurrence and one growth
base serve every shift, base point and compact set. -/
theorem finiteTranslationOrbit : FiniteTranslationOrbitStatement.{uG} := by
  intro G _ _ _ η hη hfin t
  obtain ⟨E₁, hE₁⟩ := exists_orbit_recurrence η hfin t
  obtain ⟨E₂, hE₂⟩ := exists_orbit_recurrence η hfin t⁻¹
  let B : ℝ := max 1 (max (∑ i, ‖E₁.coeffs i‖) (∑ i, ‖E₂.coeffs i‖))
  have hB : 1 ≤ B := le_max_left _ _
  have hB₁ : ∑ i, ‖E₁.coeffs i‖ ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hB₂ : ∑ i, ‖E₂.coeffs i‖ ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨E₁, B, hB, fun k a => ?_, fun K hK => ?_⟩
  · have hfun : (fun n : ℕ => η (t ^ ((n : ℤ) + k) * a)) =
        fun n : ℕ => η (t ^ n * (t ^ k * a)) := by
      funext n
      rw [zpow_add, zpow_natCast, mul_assoc]
    rw [hfun]
    exact hE₁ (t ^ k * a)
  · obtain ⟨C₁, hC₁0, hC₁⟩ := exists_orbit_initial_bound hη t E₁.order hK
    obtain ⟨C₂, hC₂0, hC₂⟩ := exists_orbit_initial_bound hη t⁻¹ E₂.order hK
    have hC0 : 0 ≤ max C₁ C₂ := le_max_of_le_left hC₁0
    refine ⟨max C₁ C₂ + 1, by linarith, fun n u hu => ?_⟩
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · rw [zpow_natCast, Int.natAbs_natCast]
      exact norm_le_of_isSolution E₁ (hE₁ u) hB hB₁ (by linarith)
        (fun i hi => (hC₁ i hi u hu).trans (by linarith [le_max_left C₁ C₂])) m
    · rw [zpow_neg, zpow_natCast, ← inv_pow, Int.natAbs_neg, Int.natAbs_natCast]
      exact norm_le_of_isSolution E₂ (hE₂ u) hB hB₂ (by linarith)
        (fun i hi => (hC₂ i hi u hu).trans (by linarith [le_max_right C₁ C₂])) m

end Langlands.HarmonicAnalysis
