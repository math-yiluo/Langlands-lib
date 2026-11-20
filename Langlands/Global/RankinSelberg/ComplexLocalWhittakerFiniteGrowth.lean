import Langlands.Global.RankinSelberg.ComplexLocalWhittakerMatrixDifferential
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerChangeCharacter

/-! # Moderate growth for finite families of local complex coefficients -/

noncomputable section

open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean Langlands.Archimedean.ComplexLocalCasimir
open Langlands.LocalFactor.Archimedean
open ComplexCharacterChange (complexMatrixHeight_mul_le)
open ComplexPlaceAnalytic (two_le_complexMatrixHeight)

attribute [local instance 100] LieRing.ofAssociativeRing

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "I" => Fin (r + 1)
local notation "M" => Matrix I I ℂ
local notation "R" => rightDerivative (matrixModel ℂ (r + 1))
local notation "Std" => Automorphic.complexStandardKFinite (r + 1)

private theorem one_le_height (g : G) : 1 ≤ complexMatrixHeight g :=
  le_trans (by norm_num) (two_le_complexMatrixHeight (by omega) g)

/-- Finitely many inducing vectors have a common moderate-growth bound. -/
theorem exists_complexWhittaker_finite_growth {J : Type*} [Fintype J]
    {ds : List ComplexCharacterData} {a : ℂˣ} {B : Std ds →ₗ[ℂ] (G → ℂ)}
    (hB : IsComplexWhittakerIntertwiner r ds a B) (f : J → Std ds) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ j g, ‖B (f j) g‖ ≤ C * complexMatrixHeight g ^ N := by
  classical
  have h := fun j => hB.2.2.1 (f j)
  choose C N h using h
  refine ⟨∑ j, max (C j) 0, Finset.univ.sup N,
    Finset.sum_nonneg fun _ _ => le_max_right _ _, fun j g => ?_⟩
  have hC : max (C j) 0 ≤ ∑ j, max (C j) 0 :=
    Finset.single_le_sum (f := fun j => max (C j) 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_univ j)
  have hN : N j ≤ Finset.univ.sup N := Finset.le_sup (Finset.mem_univ j)
  have hg : 0 ≤ complexMatrixHeight g := zero_le_one.trans (one_le_height g)
  calc
    _ ≤ C j * complexMatrixHeight g ^ N j := h j g
    _ ≤ max (C j) 0 * complexMatrixHeight g ^ N j :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hg _)
    _ ≤ _ := mul_le_mul hC (pow_le_pow_right₀ (one_le_height g) hN)
      (pow_nonneg hg _) (Finset.sum_nonneg fun _ _ => le_max_right _ _)

theorem continuous_complexMatrixHeight : Continuous (complexMatrixHeight : G → ℝ) := by
  unfold complexMatrixHeight
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  let f : ContinuousMap G ℂ := GeneralLinear.entry i j
  change Continuous fun g : G => ‖f g‖ ^ 2 + ‖f g⁻¹‖ ^ 2
  exact (f.continuous.norm.pow 2).add ((f.continuous.comp continuous_inv).norm.pow 2)

/-- A common height bound for finitely many coefficients and their first
right derivatives in the real coordinate directions. -/
theorem exists_complexWhittaker_finite_first_growth {J : Type*} [Fintype J]
    {ds : List ComplexCharacterData} {a : ℂˣ} {B : Std ds →ₗ[ℂ] (G → ℂ)}
    (hB : IsComplexWhittakerIntertwiner r ds a B) (f : J → Std ds) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
      (∀ j g, ‖B (f j) g‖ ≤ C * complexMatrixHeight g ^ N) ∧
      (∀ j (i : Bool × I × I) g,
        ‖R (matrixRealBasis (r + 1) i) (B (f j)) g‖ ≤ C * complexMatrixHeight g ^ N) := by
  let A := envelopingAction (complexStandardLie (r + 1) ds)
  let Y (i : Bool × I × I) := matrixRealBasis (r + 1) i
  let v (j : J) (i : Bool × I × I) := A (realGenerator (r + 1) (Y i)) (f j)
  let family : J ⊕ (J × (Bool × I × I)) → Std ds :=
    Sum.elim f fun p => v p.1 p.2
  obtain ⟨C, N, hC, hbound⟩ := exists_complexWhittaker_finite_growth hB family
  refine ⟨C, N, hC, fun j g => hbound (Sum.inl j) g, fun j i g => ?_⟩
  have he := congrFun (hB.2.2.2.2 (Y i) (f j) (v j i) (realGenerator_action ds _ _)) g
  change ‖R (Y i) (B (f j)) g‖ ≤ _
  rw [← he]
  exact hbound (Sum.inr (j, i)) g

/-- The first matrix jets of a finite coefficient family, on a fixed compact
part of the matrix chart, have a common growth exponent under left translation. -/
theorem exists_complexWhittaker_compact_first_jet_growth {J : Type*} [Fintype J]
    {ds : List ComplexCharacterData} {a : ℂˣ} {B : Std ds →ₗ[ℂ] (G → ℂ)}
    (hB : IsComplexWhittakerIntertwiner r ds a B) (f : J → Std ds)
    (S : Set G) (hS : IsCompact S) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ j g h, h ∈ S →
      ‖B (f j) (g * h)‖ ≤ C * complexMatrixHeight g ^ N ∧
      ‖fderiv ℝ (unitsExtension (fun k => B (f j) (g * k))) h.val‖ ≤
        C * complexMatrixHeight g ^ N := by
  obtain ⟨C, N, hC, hcoef, hder⟩ := exists_complexWhittaker_finite_first_growth hB f
  obtain ⟨H, hH⟩ := hS.exists_bound_of_continuousOn continuous_complexMatrixHeight.continuousOn
  have hcinv : Continuous (fun h : G => (h⁻¹).val) := Units.continuous_val.comp continuous_inv
  obtain ⟨D, hD⟩ := hS.exists_bound_of_continuousOn hcinv.continuousOn
  let H₀ := max H 1
  let D₀ := max D 1
  let e := matrixRealBasis (r + 1)
  let coord (p : Bool × I × I) : M →L[ℝ] ℝ := (e.coord p).toContinuousLinearMap
  let K := ∑ p : Bool × I × I, ‖coord p‖
  let C₀ := C * H₀ ^ N
  let C₁ := C₀ * max 1 (K * D₀)
  have hH₀ : 0 ≤ H₀ := zero_le_one.trans (le_max_right _ _)
  have hD₀ : 0 ≤ D₀ := zero_le_one.trans (le_max_right _ _)
  have hC₀ : 0 ≤ C₀ := mul_nonneg hC (pow_nonneg hH₀ _)
  have hC₁ : 0 ≤ C₁ := mul_nonneg hC₀ (zero_le_one.trans (le_max_left _ _))
  have hgrowth (g h : G) (hh : h ∈ S) :
      C * complexMatrixHeight (g * h) ^ N ≤ C₀ * complexMatrixHeight g ^ N := by
    have hg : 0 ≤ complexMatrixHeight g := zero_le_one.trans (one_le_height g)
    have hh' : complexMatrixHeight h ≤ H₀ := by
      have hb := hH h hh
      rw [Real.norm_of_nonneg (zero_le_one.trans (one_le_height h))] at hb
      exact hb.trans (le_max_left _ _)
    have hprod := (complexMatrixHeight_mul_le g h).trans (mul_le_mul_of_nonneg_left hh' hg)
    calc
      _ ≤ C * (complexMatrixHeight g * H₀) ^ N :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (zero_le_one.trans (one_le_height (g * h))) hprod _) hC
      _ = _ := by rw [mul_pow]; unfold C₀; ring
  refine ⟨C₁, N, hC₁, fun j g h hh => ⟨?_, ?_⟩⟩
  · refine (hcoef j (g * h)).trans ((hgrowth g h hh).trans ?_)
    have hle : C₀ ≤ C₁ := le_mul_of_one_le_right hC₀ (le_max_left _ _)
    exact mul_le_mul_of_nonneg_right hle (pow_nonneg (zero_le_one.trans (one_le_height g)) _)
  · let u := unitsExtension (fun k => B (f j) (g * k))
    let F := fderiv ℝ u h.val
    change ‖F‖ ≤ C₁ * complexMatrixHeight g ^ N
    apply F.opNorm_le_bound
      (mul_nonneg hC₁ (pow_nonneg (zero_le_one.trans (one_le_height g)) _))
    intro X
    let Y := h.inv * X
    have hX : (∑ p : Bool × I × I, coord p Y • (h.val * e p)) = X := by
      simp only [← Matrix.mul_smul, ← Matrix.mul_sum]
      change h.val * (∑ p : Bool × I × I, e.repr Y p • e p) = X
      rw [e.sum_repr, show Y = h.inv * X from rfl, ← Matrix.mul_assoc, h.val_inv, Matrix.one_mul]
    have hYn : ‖Y‖ ≤ D₀ * ‖X‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((hD h hh).trans (le_max_left _ _))
        (norm_nonneg _))
    have hDerv (p : Bool × I × I) : ‖F (h.val * e p)‖ ≤ C₀ * complexMatrixHeight g ^ N := by
      have hp := (hder j p (g * h)).trans (hgrowth g h hh)
      rw [← matrixDirectionalDerivative_unitsExtension (e p) (hB.2.1 (f j)) g h] at hp
      exact hp
    calc
      ‖F X‖ = ‖∑ p : Bool × I × I, coord p Y • F (h.val * e p)‖ := by
        simp only [← map_smul, ← map_sum, hX]
      _ ≤ ∑ p : Bool × I × I, ‖coord p Y • F (h.val * e p)‖ := norm_sum_le _ _
      _ ≤ ∑ p : Bool × I × I,
          (‖coord p‖ * (D₀ * ‖X‖)) * (C₀ * complexMatrixHeight g ^ N) := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [norm_smul]
        exact mul_le_mul ((coord p).le_opNorm Y |>.trans
          (mul_le_mul_of_nonneg_left hYn (norm_nonneg _))) (hDerv p) (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (mul_nonneg hD₀ (norm_nonneg _)))
      _ = C₀ * (K * D₀) * complexMatrixHeight g ^ N * ‖X‖ := by
        simp only [K, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun _ _ => ?_
        ring
      _ ≤ _ := by
        have hle : C₀ * (K * D₀) ≤ C₁ := mul_le_mul_of_nonneg_left (le_max_right _ _) hC₀
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hle (pow_nonneg (zero_le_one.trans (one_le_height g)) _))
          (norm_nonneg _)

end Langlands.Global.RankinSelbergGlobal
