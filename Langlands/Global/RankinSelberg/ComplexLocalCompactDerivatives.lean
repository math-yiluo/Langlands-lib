import Langlands.Representation.Archimedean.PrincipalSeriesStability
import Langlands.Analysis.CompactWeightedIntegral
import Langlands.Analysis.CompactParameterSmoothness

/-! # Right differentiation of compactly averaged complex coefficients -/

noncomputable section

open MeasureTheory Langlands.Archimedean Langlands.Analysis
open scoped Manifold ContDiff Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "I" => matrixModel ℂ n

/-- A weighted average of left translates parametrized by a compact space. -/
def complexCompactAverage (ν : Measure X) (κ : C(X, ℂ)) (j : C(X, G))
    (f : G → ℂ) (g : G) : ℂ :=
  ∫ k, κ k * f (j k * g) ∂ν

private theorem rightDerivative_left_mul (Y : Mat) (f : G → ℂ) (z g : G) :
    rightDerivative I Y (fun u => f (z * u)) g = rightDerivative I Y f (z * g) := by
  unfold rightDerivative
  have he : (fun h : G => f (z * (g * h))) = fun h : G => f (z * g * h) :=
    funext fun h => congrArg f (mul_assoc z g h).symm
  rw [he]
  rfl

/-- A compact left average preserves smoothness and commutes with all real
right derivatives. -/
def ComplexLocalCompactDerivativesStatement (n : ℕ) : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    (κ : C(X, ℂ)) (j : C(X, Langlands.GeneralLinear n ℂ))
    (f : Langlands.GeneralLinear n ℂ → ℂ),
    ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ f →
    ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ (complexCompactAverage ν κ j f) ∧
      ∀ Y : Matrix (Fin n) (Fin n) ℂ,
        rightDerivative (matrixModel ℂ n) Y (complexCompactAverage ν κ j f) =
          complexCompactAverage ν κ j (rightDerivative (matrixModel ℂ n) Y f)

theorem complexLocalCompactDerivatives : ComplexLocalCompactDerivativesStatement n := by
  intro K _ _ _ _ ν _ κ j f hf
  classical
  let S : Set Mat := {y | IsUnit y}
  have hS : IsOpen S := isOpen_setOf_isUnit_matrix
  let jM : C(K, Mat) := ⟨fun k => (j k).val, Units.continuous_val.comp j.continuous⟩
  have hj (k : K) : jM k ∈ S := (j k).isUnit
  let h (p : Mat × Mat) := unitsExtension f (p.2 * p.1)
  have hh : ContDiffOn ℝ ∞ h (S ×ˢ S) :=
    (contDiffOn_unitsExtension hf).comp (contDiff_snd.mul contDiff_fst).contDiffOn
      (fun _ hp => hp.2.mul hp.1)
  let F (y : Mat) : C(K, ℂ) :=
    if hy : y ∈ S then
      ⟨fun k => h (y, jM k), hh.continuousOn.comp_continuous
        (continuous_const.prodMk jM.continuous) (fun k => ⟨hy, hj k⟩)⟩
    else 0
  have hF (y : Mat) (hy : y ∈ S) (k : K) : F y k = h (y, jM k) := by
    simp only [F, dite_eq_left hy, ContinuousMap.coe_mk]
  have hFam : ContDiffOn ℝ ∞ F S :=
    contDiffOn_infty_compactFamily_of_joint jM hS hS hj hh hF
  let T := (compactWeightedIntegral ν κ).restrictScalars ℝ
  let avg := complexCompactAverage ν κ j f
  have hEq (y : Mat) (hy : y ∈ S) : unitsExtension avg y = T (F y) := by
    obtain ⟨g, rfl⟩ := hy
    rw [unitsExtension_val]
    change _ = compactWeightedIntegral ν κ (F g.val)
    rw [compactWeightedIntegral_apply]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun k => ?_
    simp only [hF _ g.isUnit, h, jM, ContinuousMap.coe_mk,
      ← Units.val_mul, unitsExtension_val, smul_eq_mul, mul_comm]
  have hSm : ContMDiff I 𝓘(ℝ, ℂ) ∞ avg :=
    contMDiff_of_contDiffOn ((T.contDiff.comp_contDiffOn hFam).congr hEq)
      (fun g => (unitsExtension_val avg g).symm)
  refine ⟨hSm, fun Y => funext fun g => ?_⟩
  have hgd : HasFDerivAt F (fderiv ℝ F g.val) g.val :=
    ((hFam.contDiffAt (hS.mem_nhds g.isUnit)).differentiableAt (by simp)).hasFDerivAt
  have hev : unitsExtension avg =ᶠ[𝓝 g.val] T ∘ F :=
    Filter.mem_of_superset (hS.mem_nhds g.isUnit) fun y hy => hEq y hy
  change rightDerivative I Y avg g = complexCompactAverage ν κ j (rightDerivative I Y f) g
  rw [rightDerivative_eq_fderiv hSm, hev.fderiv_eq, (T.hasFDerivAt.comp g.val hgd).fderiv]
  change compactWeightedIntegral ν κ (fderiv ℝ F g.val (g.val * Y)) = _
  rw [compactWeightedIntegral_apply]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun k => ?_
  let E := (ContinuousMap.evalCLM ℂ (M := ℂ) k).restrictScalars ℝ
  let fk (u : G) := f (j k * u)
  have hfk : ContMDiff I 𝓘(ℝ, ℂ) ∞ fk := hf.comp contMDiff_mul_left
  have hfe : E ∘ F =ᶠ[𝓝 g.val] unitsExtension fk := by
    filter_upwards [hS.mem_nhds g.isUnit] with y hy
    obtain ⟨u, rfl⟩ := hy
    change (F u.val) k = unitsExtension fk u.val
    simp only [hF _ u.isUnit, h, jM, ContinuousMap.coe_mk, ← Units.val_mul,
      unitsExtension_val, fk]
  have hd := (E.hasFDerivAt.comp g.val hgd).fderiv
  rw [hfe.fderiv_eq] at hd
  have hh' := congrArg (fun L : Mat →L[ℝ] ℂ => L (g.val * Y)) hd
  change fderiv ℝ (unitsExtension fk) g.val (g.val * Y) =
    (fderiv ℝ F g.val (g.val * Y)) k at hh'
  change (fderiv ℝ F g.val (g.val * Y)) k • κ k =
    κ k * rightDerivative I Y f (j k * g)
  rw [← rightDerivative_left_mul Y f (j k) g, rightDerivative_eq_fderiv hfk, hh', smul_eq_mul, mul_comm]

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
