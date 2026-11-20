import Langlands.Global.RankinSelberg.ComplexLocalHessianAnalytic
import Langlands.Global.RankinSelberg.ComplexLocalSquareSpectrum

/-! # Real analyticity of smooth images of complex principal series vectors -/

noncomputable section

open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean Langlands.Archimedean.ComplexLocalCasimir
open Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}
local notation "I" => Fin n
local notation "M" => Matrix I I ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Std" => Automorphic.complexStandardKFinite n
local notation "R" => rightDerivative (matrixModel ℂ n)

private theorem hessian_pair_eq_rightDerivative {W : G → ℂ}
    (hW : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ W)
    (hRW : ∀ X : M, ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (R X W))
    (g : G) (i j : I) :
    let X : M := Matrix.single i j 1
    let Y : M := Matrix.single i j Complex.I
    let H := fderiv ℝ (fderiv ℝ (unitsExtension W)) g.val
    H (g.val * Y) (g.val * Y) + H (g.val * X) (g.val * X) =
      R X (R X W) g + R Y (R Y W) g := by
  intro X Y H
  let F := unitsExtension W
  have hF : ContDiffAt ℝ ∞ F g.val :=
    ((contDiffOn_unitsExtension hW) g.val g.isUnit).contDiffAt
      (isOpen_setOf_isUnit_matrix.mem_nhds g.isUnit)
  have hder (Z : M) : R Z (R Z W) g =
      matrixDirectionalDerivative Z (matrixDirectionalDerivative Z F) g.val := by
    simpa only [one_mul] using
      (matrixDirectionalDerivative_twice_unitsExtension Z hW (hRW Z) 1 g).symm
  have hY : Y = Complex.I • X := by simp [X, Y, Matrix.smul_single]
  have hcancel : g.val * Y * Y = -(g.val * X * X) := by
    simp only [hY, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [hder X, hder Y, matrixDirectionalDerivative_twice X hF,
    matrixDirectionalDerivative_twice Y hF, hcancel, map_neg]
  change H _ _ + H _ _ = (H _ _ + _) + (H _ _ - _)
  abel

private theorem hessian_of_standardLie_intertwining {ds : List ComplexCharacterData}
    (A : Std ds →ₗ[ℂ] (G → ℂ))
    (hA : ∀ f, ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (A f))
    (hder : ∀ (X : M) (f : Std ds),
      A (envelopingAction (complexStandardLie n ds) (realGenerator n X) f) = R X (A f))
    (f : Std ds) (g : G) :
    complexCoordinateHessianSum (unitsExtension (A f)) g.val =
      A (coordinateSquareOperator ds f) g := by
  let E := envelopingAction (complexStandardLie n ds)
  have hR (Z : M) : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (R Z (A f)) :=
    hder Z f ▸ hA (E (realGenerator n Z) f)
  have hsq (Z : M) : A (E (realGenerator n Z ^ 2) f) g = R Z (R Z (A f)) g := by
    rw [map_pow, pow_two, Module.End.mul_apply, hder, hder]
  simp only [complexCoordinateHessianSum, Fintype.sum_prod_type, matrixRealBasis_apply,
    Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
  simp only [coordinateSquareOperator, coordinateSquareSum, map_add, map_sum,
    LinearMap.add_apply, LinearMap.sum_apply, Pi.add_apply, Finset.sum_apply]
  change _ =
    (∑ i : I, ∑ j : I, A (E (realGenerator n (Matrix.single i j 1) ^ 2) f) g) +
      (∑ i : I, ∑ j : I, A (E (realGenerator n (Matrix.single i j Complex.I) ^ 2) f) g)
  simp_rw [hsq]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    hessian_pair_eq_rightDerivative (hA f) hR g i j

/-- A smooth linear image commuting with right Lie derivatives is real
analytic on the open set of invertible matrices. -/
theorem analyticOnNhd_unitsExtension_of_standardLie_intertwining {ds : List ComplexCharacterData}
    (A : Std ds →ₗ[ℂ] (G → ℂ))
    (hA : ∀ f, ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (A f))
    (hder : ∀ (X : M) (f : Std ds),
      A (envelopingAction (complexStandardLie n ds) (realGenerator n X) f) = R X (A f))
    (f : Std ds) :
    AnalyticOnNhd ℝ (unitsExtension (A f)) {h : M | IsUnit h} := by
  obtain ⟨m, v, a, c, hf, hv⟩ := exists_coordinateSquare_eigenvector_expansion ds f
  have han (j : Fin m) : AnalyticOnNhd ℝ (unitsExtension (A (v j))) {h : M | IsUnit h} := by
    refine analyticOnNhd_of_complexCoordinateHessianSum_eq n (c j)
      (contDiffOn_unitsExtension (hA (v j))) fun h hh => ?_
    obtain ⟨g, rfl⟩ := hh
    rw [hessian_of_standardLie_intertwining A hA hder, hv, map_smul,
      unitsExtension_val, Pi.smul_apply, smul_eq_mul]
  have hsum : AnalyticOnNhd ℝ
      (fun h : M => ∑ j, a j * unitsExtension (A (v j)) h) {h | IsUnit h} :=
    Finset.analyticOnNhd_fun_sum _ fun j _ => analyticOnNhd_const.mul (han j)
  refine hsum.congr isOpen_setOf_isUnit_matrix fun h hh => ?_
  obtain ⟨g, rfl⟩ := hh
  rw [unitsExtension_val, hf, map_sum]
  simp only [Finset.sum_apply, unitsExtension_val, map_smul, Pi.smul_apply, smul_eq_mul]

variable (n) in
/-- Smooth outputs of a linear map intertwining the standard real Lie
actions are analytic in the invertible matrix chart. -/
def ComplexLocalIntertwinerAnalyticStatement : Prop :=
  ∀ (ds : List ComplexCharacterData) (A : Std ds →ₗ[ℂ] (G → ℂ)),
    (∀ f, ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (A f)) →
    (∀ (X : M) (f : Std ds),
      A (envelopingAction (complexStandardLie n ds) (realGenerator n X) f) = R X (A f)) →
    ∀ f : Std ds, AnalyticOnNhd ℝ (unitsExtension (A f)) {h : M | IsUnit h}

theorem complexLocalIntertwinerAnalytic (n : ℕ) : ComplexLocalIntertwinerAnalyticStatement n :=
  fun _ A => analyticOnNhd_unitsExtension_of_standardLie_intertwining A

/-- The Whittaker coefficients of an actual complex intertwiner are real analytic. -/
theorem analyticOnNhd_unitsExtension_complexWhittaker {r : ℕ} {ds : List ComplexCharacterData}
    {a : ℂˣ}
    {B : Automorphic.complexStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℂ → ℂ)}
    (hB : IsComplexWhittakerIntertwiner r ds a B)
    (f : Automorphic.complexStandardKFinite (r + 1) ds) :
    AnalyticOnNhd ℝ (unitsExtension (B f))
      {h : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ | IsUnit h} :=
  analyticOnNhd_unitsExtension_of_standardLie_intertwining B hB.2.1
    (fun X v => hB.2.2.2.2 X v _ (realGenerator_action ds X v)) f

end Langlands.Global.RankinSelbergGlobal
