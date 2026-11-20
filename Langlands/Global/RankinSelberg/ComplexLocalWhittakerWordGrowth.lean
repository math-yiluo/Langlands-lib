import Langlands.Global.RankinSelberg.ComplexLocalWhittakerJetGrowth
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerRootDerivative

/-! # A common growth exponent for all right derivative words -/

noncomputable section

open Filter
open scoped ContDiff Manifold Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexLocalConvergence

open Langlands.Archimedean Langlands.LocalFactor.Archimedean

variable {r : ℕ}
local notation "I" => Fin (r + 1)
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "M" => Matrix I I ℂ
local notation "Std" => Automorphic.complexStandardKFinite (r + 1)

private theorem matrixField_jet_le (X : M) (p : ℕ) :
    ‖iteratedFDeriv ℝ p (fun h : M => h * X) (1 : M)‖ ≤ ‖X‖ := by
  let L : M →L[ℝ] M := (ContinuousLinearMap.mul ℝ M).flip X
  change ‖iteratedFDeriv ℝ p (L : M → M) (1 : M)‖ ≤ _
  cases p with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    change ‖(1 : M) * X‖ ≤ ‖X‖
    rw [Matrix.one_mul]
  | succ p =>
    rw [← norm_iteratedFDeriv_fderiv, show fderiv ℝ (L : M → M) = fun _ => L from
      funext fun x => L.fderiv]
    cases p with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact L.opNorm_le_bound (norm_nonneg _) fun x =>
        (norm_mul_le x X).trans_eq (mul_comm _ _)
    | succ p =>
      rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero p), Pi.zero_apply, norm_zero]
      exact norm_nonneg _

private theorem matrixDirectionalDerivative_jet_le (X : M) {u : M → ℂ}
    (hu : ContDiffOn ℝ ∞ u {h : M | IsUnit h}) (p : ℕ) :
    ‖iteratedFDeriv ℝ p (matrixDirectionalDerivative X u) (1 : M)‖ ≤
      ∑ j ∈ Finset.range (p + 1),
        (p.choose j : ℝ) * ‖iteratedFDeriv ℝ (j + 1) u (1 : M)‖ * ‖X‖ := by
  let S : Set M := {h | IsUnit h}
  have hS : IsOpen S := isOpen_setOf_isUnit_matrix
  have h1 : (1 : M) ∈ S := isUnit_one
  have hfd := hu.fderiv_of_isOpen hS (show ∞ + 1 ≤ (∞ : ℕ∞ω) by simp)
  let L : M →L[ℝ] M := (ContinuousLinearMap.mul ℝ M).flip X
  have h := norm_iteratedFDerivWithin_clm_apply hfd L.contDiff.contDiffOn hS.uniqueDiffOn h1
    (show (p : ℕ∞ω) ≤ ∞ by simp)
  change ‖iteratedFDerivWithin ℝ p (matrixDirectionalDerivative X u) S 1‖ ≤ _ at h
  rw [iteratedFDerivWithin_of_isOpen p hS h1] at h
  refine h.trans (Finset.sum_le_sum fun j _ => ?_)
  rw [iteratedFDerivWithin_of_isOpen j hS h1, iteratedFDerivWithin_of_isOpen (p - j) hS h1,
    norm_iteratedFDeriv_fderiv]
  exact mul_le_mul_of_nonneg_left (matrixField_jet_le X (p - j)) (by positivity)

private theorem matrixDirectionalDerivative_standard_germ
    {ds : List ComplexCharacterData} {a : ℂˣ} {B : Std ds →ₗ[ℂ] (G → ℂ)}
    (hB : IsComplexWhittakerIntertwiner r ds a B) (f : Std ds) (X : M) (g : G) :
    matrixDirectionalDerivative X (unitsExtension (fun h => B f (g * h))) =ᶠ[𝓝 (1 : M)]
      unitsExtension (fun h => B (standardDerivative X f) (g * h)) := by
  filter_upwards [isOpen_setOf_isUnit_matrix.mem_nhds (isUnit_one : IsUnit (1 : M))] with h hh
  change IsUnit h at hh
  let hUnit : G := hh.unit
  change matrixDirectionalDerivative X (unitsExtension (fun k => B f (g * k))) hUnit.val =
      unitsExtension (fun k => B (standardDerivative X f) (g * k)) hUnit.val
  rw [matrixDirectionalDerivative_unitsExtension X (hB.2.1 f), unitsExtension_val,
    hB.2.2.2.2 X f (standardDerivative X f) rfl]

/-- A bound on the individual matrix directions gives a uniform constant at
each word length, with the same height exponent at every length. -/
theorem exists_complexWhittaker_right_word_growth
    {ds : List ComplexCharacterData} {a : ℂˣ} {B : Std ds →ₗ[ℂ] (G → ℂ)}
    (hB : IsComplexWhittakerIntertwiner r ds a B) (f : Std ds) {D : ℝ} (hD : 0 ≤ D) :
    ∃ (N : ℕ) (C : ℕ → ℝ), (∀ m, 0 ≤ C m) ∧ ∀ (w : List M),
      (∀ X ∈ w, ‖X‖ ≤ D) → ∀ g : G,
        ‖B (standardDerivativeWord w f) g‖ ≤ C w.length * complexMatrixHeight g ^ N := by
  obtain ⟨N, C₀, hC₀, hstart⟩ := exists_complexWhittaker_matrix_jet_growth hB f
  let C : ℕ → ℕ → ℝ := Nat.rec C₀ fun _ C' p =>
    ∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) * C' (j + 1) * D
  have hC (m p : ℕ) : 0 ≤ C m p := by
    induction m generalizing p with
    | zero => exact hC₀ p
    | succ m ih =>
      exact Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ih _)) hD
  let u (w : List M) (g : G) : M → ℂ :=
    unitsExtension (fun h => B (standardDerivativeWord w f) (g * h))
  have hjet (w : List M) (hw : ∀ X ∈ w, ‖X‖ ≤ D) (g : G) (p : ℕ) :
      ‖iteratedFDeriv ℝ p (u w g) (1 : M)‖ ≤ C w.length p * complexMatrixHeight g ^ N := by
    induction w generalizing p with
    | nil => exact hstart g p
    | cons X w ih =>
      have he : matrixDirectionalDerivative X (u w g) =ᶠ[𝓝 (1 : M)] u (X :: w) g :=
        matrixDirectionalDerivative_standard_germ hB (standardDerivativeWord w f) X g
      rw [← (he.iteratedFDeriv ℝ p).eq_of_nhds]
      have hsm : ContDiffOn ℝ ∞ (u w g) {h : M | IsUnit h} :=
        contDiffOn_unitsExtension ((hB.2.1 (standardDerivativeWord w f)).comp contMDiff_mul_left)
      have hi (j : ℕ) := ih (fun Y hY => hw Y (List.mem_cons_of_mem X hY)) (j + 1)
      have hX := hw X (List.mem_cons_self)
      have hg : 0 ≤ complexMatrixHeight g :=
        (by norm_num : (0 : ℝ) ≤ 2).trans
          (ComplexPlaceAnalytic.two_le_complexMatrixHeight (by omega) g)
      refine (matrixDirectionalDerivative_jet_le X hsm p).trans ?_
      change _ ≤ (∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) * C w.length (j + 1) * D) *
        complexMatrixHeight g ^ N
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      calc
        _ ≤ (p.choose j : ℝ) * (C w.length (j + 1) * complexMatrixHeight g ^ N) * D :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hi j) (Nat.cast_nonneg _)) hX
            (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
              (mul_nonneg (hC _ _) (pow_nonneg hg _)))
        _ = _ := by ring
  refine ⟨N, fun m => C m 0, fun m => hC m 0, fun w hw g => ?_⟩
  have h := hjet w hw g 0
  rw [norm_iteratedFDeriv_zero] at h
  change ‖unitsExtension (fun k => B (standardDerivativeWord w f) (g * k)) ((1 : G).val)‖ ≤ _ at h
  rwa [unitsExtension_val, mul_one] at h

end Langlands.Global.RankinSelbergGlobal.ComplexLocalConvergence
