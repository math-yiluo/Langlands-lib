import Langlands.Analysis.LocalEllipticSystemPointwise
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerEllipticChart
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerFiniteGrowth

/-! # A single growth exponent for all matrix jets of a complex Whittaker coefficient -/

noncomputable section

open Metric Set Topology
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 80000

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Analysis Langlands.Archimedean Langlands.Archimedean.ComplexLocalCasimir
open Langlands.LocalFactor.Archimedean
open ComplexPlaceAnalytic (two_le_complexMatrixHeight)

variable {r : ℕ}

local notation "n" => r + 1
local notation "I" => Fin n
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "M" => Matrix I I ℂ
local notation "E" => EuclideanSpace ℝ (Fin (Fintype.card (Bool × I × I)))
local notation "Std" => Automorphic.complexStandardKFinite n

private theorem iteratedJet_le_of_coordinates (e : M ≃L[ℝ] E) (u : M → ℂ) (p : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ p u (e.symm y)‖ ≤
      ‖iteratedFDeriv ℝ p (u ∘ e.symm) y‖ * ‖e.toContinuousLinearMap‖ ^ p := by
  have he :
      iteratedFDeriv ℝ p u (e.symm y) =
        (iteratedFDeriv ℝ p (u ∘ e.symm) y).compContinuousLinearMap
          (fun _ => e.toContinuousLinearMap) := by
    ext m
    exact (CoordinateScalarOperator.iteratedFDeriv_comp_equiv e u p y m).symm
  rw [he]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv ℝ p (u ∘ e.symm) y).norm_compContinuousLinearMap_le
      (fun _ => e.toContinuousLinearMap)

private theorem exists_jet_growth_of_finite_system {J : Type*} [Fintype J]
    {ds : List ComplexCharacterData} {a : ℂˣ} {B : Std ds →ₗ[ℂ] (G → ℂ)}
    (hB : IsComplexWhittakerIntertwiner r ds a B) (f : J → Std ds) (A : J → J → ℂ)
    (hA : ∀ i, coordinateSquareOperator ds (f i) = ∑ j, A i j • f j) :
    ∃ (N : ℕ) (C : ℕ → ℝ), (∀ p, 0 ≤ C p) ∧ ∀ i (g : G) (p : ℕ),
      ‖iteratedFDeriv ℝ p (unitsExtension (fun h => B (f i) (g * h))) (1 : M)‖ ≤
        C p * complexMatrixHeight g ^ N := by
  let D := complexEllipticChartOperator n
  let e := D.euclideanCoordinates
  let S : Set E := e.symm ⁻¹' {h : M | IsUnit h}
  let y₀ := e 1
  have hS : IsOpen S := isOpen_setOf_isUnit_matrix.preimage e.symm.continuous
  have hy₀ : y₀ ∈ S := by
    change IsUnit (e.symm (e 1))
    rw [e.symm_apply_apply]
    exact isUnit_one
  have hell : D.toEuclidean.IsEllipticOn S :=
    D.transport_isElliptic e (complexEllipticChartOperator_elliptic n)
  have han : D.toEuclidean.AnalyticCoefficientsOn S :=
    D.transport_analyticCoefficients e ((complexEllipticChartOperator_analytic n).mono
      (Set.subset_univ _))
  obtain ⟨R, _, hRsub, C, hC, hbound⟩ :=
    exists_localEllipticSystem_derivative_bounds (by decide : 0 < 2) D.toEuclidean
      D.toEuclidean_basis A hS (fun k w => (han k w).contDiffOn hS.uniqueDiffOn) hell hy₀
  let ψ : G → E := fun h => e h.val
  let U : Set G := ψ ⁻¹' closedBall y₀ R
  have hψ : IsEmbedding ψ := e.toHomeomorph.isEmbedding.comp Units.isOpenEmbedding_val.isEmbedding
  have hU : IsCompact U := hψ.isInducing.isCompact_preimage' (isCompact_closedBall _ _) (by
    intro y hy
    have hu : IsUnit (e.symm y) := hRsub hy
    exact ⟨hu.unit, e.apply_symm_apply y⟩)
  obtain ⟨M₀, N, hM₀, hjet⟩ := exists_complexWhittaker_compact_first_jet_growth hB f U hU
  let M₁ := M₀ * max 1 ‖e.symm.toContinuousLinearMap‖
  have hM₁ : 0 ≤ M₁ := mul_nonneg hM₀ (zero_le_one.trans (le_max_left _ _))
  refine ⟨N, fun p => (C p * M₁) * ‖e.toContinuousLinearMap‖ ^ p,
    fun p => mul_nonneg (mul_nonneg (hC p) hM₁) (pow_nonneg (norm_nonneg _) _),
    fun i g p => ?_⟩
  let u (j : J) : M → ℂ := unitsExtension (fun h => B (f j) (g * h))
  let v (j : J) : E → ℂ := u j ∘ e.symm
  have huo (j : J) : ContDiffOn ℝ ∞ (u j) {h : M | IsUnit h} :=
    contDiffOn_unitsExtension ((hB.2.1 (f j)).comp contMDiff_mul_left)
  have hv (j : J) : ContDiffOn ℝ ∞ (v j) S :=
    (huo j).comp e.symm.contDiff.contDiffOn (fun _ h => h)
  have hveq (j : J) (y : E) (hy : y ∈ S) :
      D.toEuclidean.action (v j) y = ∑ k, A j k * v k y := by
    have hu : IsUnit (e.symm y) := hy
    let h : G := hu.unit
    have hh : h.val = e.symm y := rfl
    change (D.transport e).action (u j ∘ e.symm) y = _
    rw [D.transport_action, complexEllipticChartOperator_action, ← hh,
      complexCoordinateHessianSum_intertwiner hB, hA]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [v, Function.comp_apply, ← hh, u, unitsExtension_val]
  have hg : 0 ≤ complexMatrixHeight g :=
    (by norm_num : (0 : ℝ) ≤ 2).trans (two_le_complexMatrixHeight (by omega) g)
  have hM : 0 ≤ M₁ * complexMatrixHeight g ^ N := mul_nonneg hM₁ (pow_nonneg hg _)
  have hinit (j : J) (q : ℕ) (hq : q < 2) (y : E) (hy : y ∈ ball y₀ R) :
      ‖iteratedFDeriv ℝ q (v j) y‖ ≤ M₁ * complexMatrixHeight g ^ N := by
    have hcy : y ∈ closedBall y₀ R := ball_subset_closedBall hy
    have hu : IsUnit (e.symm y) := hRsub hcy
    let h : G := hu.unit
    have hh : h.val = e.symm y := rfl
    have hhU : h ∈ U := by
      change e h.val ∈ closedBall y₀ R
      rwa [hh, e.apply_symm_apply]
    obtain ⟨hval, hfd⟩ := hjet j g h hhU
    have hc : M₀ ≤ M₁ := le_mul_of_one_le_right hM₀ (le_max_left _ _)
    have hc' : M₀ * ‖e.symm.toContinuousLinearMap‖ ≤ M₁ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hM₀
    interval_cases q
    · rw [norm_iteratedFDeriv_zero]
      change ‖u j (e.symm y)‖ ≤ _
      rw [← hh]
      change ‖unitsExtension (fun k => B (f j) (g * k)) h.val‖ ≤ _
      rw [unitsExtension_val]
      exact hval.trans (mul_le_mul_of_nonneg_right hc (pow_nonneg hg _))
    · rw [norm_iteratedFDeriv_one]
      have hdiff : DifferentiableAt ℝ (u j) (e.symm y) :=
        ((huo j).contDiffAt (isOpen_setOf_isUnit_matrix.mem_nhds hu)).differentiableAt (by simp)
      change ‖fderiv ℝ (u j ∘ e.symm) y‖ ≤ _
      rw [fderiv_comp y hdiff e.symm.differentiableAt]
      change ‖(fderiv ℝ (u j) (e.symm y)).comp (fderiv ℝ (e.symm.toContinuousLinearMap) y)‖ ≤ _
      rw [ContinuousLinearMap.fderiv, ← hh]
      calc
        _ ≤ ‖fderiv ℝ (u j) h.val‖ * ‖e.symm.toContinuousLinearMap‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (M₀ * complexMatrixHeight g ^ N) * ‖e.symm.toContinuousLinearMap‖ :=
          mul_le_mul_of_nonneg_right hfd (norm_nonneg _)
        _ ≤ M₁ * complexMatrixHeight g ^ N := by
          rw [mul_right_comm]
          exact mul_le_mul_of_nonneg_right hc' (pow_nonneg hg _)
  have hj := hbound v hv hveq (M₁ * complexMatrixHeight g ^ N) hinit i p
  rw [max_eq_right hM] at hj
  calc
    _ ≤ ‖iteratedFDeriv ℝ p (v i) y₀‖ * ‖e.toContinuousLinearMap‖ ^ p := by
      simpa only [y₀, e.symm_apply_apply] using iteratedJet_le_of_coordinates e (u i) p y₀
    _ ≤ (C p * (M₁ * complexMatrixHeight g ^ N)) * ‖e.toContinuousLinearMap‖ ^ p :=
      mul_le_mul_of_nonneg_right hj (pow_nonneg (norm_nonneg _) _)
    _ = _ := by ring

/-- All matrix jets at the identity of the left translates of a fixed
Whittaker coefficient have a common polynomial height exponent. -/
theorem exists_complexWhittaker_matrix_jet_growth
    {ds : List ComplexCharacterData} {a : ℂˣ} {B : Std ds →ₗ[ℂ] (G → ℂ)}
    (hB : IsComplexWhittakerIntertwiner r ds a B) (f : Std ds) :
    ∃ (N : ℕ) (C : ℕ → ℝ), (∀ p, 0 ≤ C p) ∧ ∀ (g : G) (p : ℕ),
      ‖iteratedFDeriv ℝ p (unitsExtension (fun h => B f (g * h))) (1 : M)‖ ≤
        C p * complexMatrixHeight g ^ N := by
  obtain ⟨V, hdim, hf, hV⟩ := exists_invariant_coordinateSquareOperator_submodule ds f
  let : FiniteDimensional ℂ V := hdim
  let : Module.Free ℂ V := Module.Free.of_divisionRing ℂ V
  let J := Fin (Module.finrank ℂ V)
  let e : Module.Basis J ℂ V := Module.finBasis ℂ V
  let v (j : Option J) : V := j.elim ⟨f, hf⟩ e
  let w (j : Option J) : V :=
    ⟨coordinateSquareOperator ds (v j), hV (v j) (v j).property⟩
  let A (i j : Option J) : ℂ := j.elim 0 (e.repr (w i))
  have hA (i : Option J) :
      coordinateSquareOperator ds (v i : Std ds) = ∑ j, A i j • (v j : Std ds) := by
    have hw := congrArg V.subtype (e.sum_repr (w i))
    simp only [map_sum, map_smul, Submodule.subtype_apply] at hw
    rw [Fintype.sum_option]
    simpa only [A, v, Option.elim_none, Option.elim_some, zero_smul, zero_add] using hw.symm
  obtain ⟨N, C, hC, hjet⟩ := exists_jet_growth_of_finite_system hB (fun j => (v j : Std ds)) A hA
  exact ⟨N, C, hC, hjet none⟩

end Langlands.Global.RankinSelbergGlobal
