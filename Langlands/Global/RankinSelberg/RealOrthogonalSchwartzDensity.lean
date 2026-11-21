import Langlands.Analysis.SchwartzCompactAverage
import Langlands.Analysis.SchwartzScaledCutoff
import Langlands.Representation.Archimedean.OrthogonalFinitePolynomial
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.Topology.Sequences

/-! # Density of left orthogonal finite real square Schwartz functions -/

noncomputable section

open MeasureTheory Set
open scoped Classical Matrix.Norms.Operator SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open Langlands.Analysis (dense_hasCompactSupport_schwartz)
open Langlands.Analysis.SchwartzCompactAverage (average mem_closure_average_of_dense)
open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.OrthogonalFinitePolynomial (polynomialStar polynomialStar_toSubalgebra
  polynomialStar_separatesPoints separated inv_mul_mem_separated integrable_of_continuous)

variable {n : ℕ}
local notation "U" => Matrix.unitaryGroup (Fin n) ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "Haar" => (Measure.haar : Measure U)

private def leftAction : Mat →ₗ[ℝ] (Mat →L[ℝ] Mat) where
  toFun A := (mulLeftLinearMap (Fin n) ℝ A).toContinuousLinearMap
  map_add' A B := by ext X i j; exact congrArg (fun M : Mat => M i j) (Matrix.add_mul A B X)
  map_smul' c A := by ext X i j; exact congrArg (fun M : Mat => M i j) (Matrix.smul_mul c A X)

private def leftPullback (k : U) : Mat →L[ℝ] Mat := leftAction k⁻¹.val

private theorem continuous_leftPullback : Continuous (leftPullback (n := n)) :=
  leftAction.toContinuousLinearMap.continuous.comp (continuous_subtype_val.comp continuous_inv)

private theorem leftPullback_one : leftPullback (1 : U) = ContinuousLinearMap.id ℝ Mat := by
  ext X i j
  change ((1 : U)⁻¹.val * X) i j = X i j
  rw [inv_one, OneMemClass.coe_one, Matrix.one_mul]

private theorem leftPullback_inverse (k : U) (X : Mat) :
    leftPullback k⁻¹ (leftPullback k X) = X := by
  change (k⁻¹⁻¹ : U).val * ((k⁻¹ : U).val * X) = X
  rw [inv_inv, ← Matrix.mul_assoc, ← Matrix.UnitaryGroup.mul_val, mul_inv_cancel,
    OneMemClass.coe_one, Matrix.one_mul]

private theorem exists_leftPullback_lower :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : Mat) (k : U), ‖X‖ ≤ C * ‖leftPullback k X‖ := by
  obtain ⟨B, hB⟩ := (isCompact_univ.image (continuous_leftPullback (n := n)).norm).bddAbove
  refine ⟨max B 0, le_max_right _ _, fun X k => ?_⟩
  have hb : ‖leftPullback k⁻¹‖ ≤ max B 0 :=
    (hB ⟨k⁻¹, mem_univ _, rfl⟩).trans (le_max_left _ _)
  conv_lhs => rw [← leftPullback_inverse k X]
  exact ((leftPullback k⁻¹).le_opNorm _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

private def leftAverage (Φ : 𝓢(Mat, ℂ)) (w : C(U, ℂ)) : 𝓢(Mat, ℂ) :=
  average w leftPullback Φ Haar w.continuous continuous_leftPullback
    (Classical.choose_spec exists_leftPullback_lower).1
    (Classical.choose_spec exists_leftPullback_lower).2

private theorem leftAverage_apply (Φ : 𝓢(Mat, ℂ)) (w : C(U, ℂ)) (X : Mat) :
    leftAverage Φ w X = ∫ k : U, w k * Φ (k⁻¹.val * X) ∂Haar := rfl

private def separatedIntegral (Φ : 𝓢(Mat, ℂ)) (w : U → U → ℂ) (k : U) (X : Mat) : ℂ :=
  ∫ v : U, w k v * Φ (v⁻¹.val * X) ∂Haar

private theorem separatedIntegral_finite (Φ : 𝓢(Mat, ℂ)) {w : U → U → ℂ}
    (hw : w ∈ separated n) : (∀ k, Continuous (w k)) ∧
      ∃ S : Submodule ℂ (Mat → ℂ), FiniteDimensional ℂ S ∧ ∀ k, separatedIntegral Φ w k ∈ S := by
  have hΦ (X : Mat) : Continuous (fun u : U => Φ (u⁻¹.val * X)) :=
    Φ.continuous.comp ((continuous_subtype_val.comp continuous_inv).matrix_mul continuous_const)
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨α, _, β, rfl⟩ := hw
    let f : Mat → ℂ := fun X => ∫ v : U, β v * Φ (v⁻¹.val * X) ∂Haar
    refine ⟨fun k => continuous_const.mul β.continuous, ℂ ∙ f, inferInstance, fun k => ?_⟩
    have he : separatedIntegral Φ (fun k v => α k * β v) k = α k • f := by
      funext X
      simp only [separatedIntegral, mul_assoc, integral_const_mul, Pi.smul_apply, smul_eq_mul, f]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self f)
  | zero =>
    refine ⟨fun _ => continuous_const, ⊥, inferInstance, fun k => ?_⟩
    rw [Submodule.mem_bot]
    funext X
    simp [separatedIntegral]
  | add w v _ _ hw hv =>
    obtain ⟨hwc, S, hS, hwS⟩ := hw
    obtain ⟨hvc, T, hT, hvT⟩ := hv
    let : FiniteDimensional ℂ S := hS
    let : FiniteDimensional ℂ T := hT
    refine ⟨fun k => (hwc k).add (hvc k), S ⊔ T, inferInstance, fun k => ?_⟩
    have he : separatedIntegral Φ (w + v) k = separatedIntegral Φ w k + separatedIntegral Φ v k := by
      funext X
      simp only [separatedIntegral, Pi.add_apply, add_mul]
      exact integral_add (integrable_of_continuous Haar ((hwc k).mul (hΦ X)))
        (integrable_of_continuous Haar ((hvc k).mul (hΦ X)))
    rw [he]
    exact Submodule.add_mem _ ((le_sup_left : S ≤ S ⊔ T) (hwS k)) ((le_sup_right : T ≤ S ⊔ T) (hvT k))
  | smul c w _ hw =>
    obtain ⟨hwc, S, hS, hwS⟩ := hw
    refine ⟨fun k => (hwc k).const_smul c, S, hS, fun k => ?_⟩
    have he : separatedIntegral Φ (c • w) k = c • separatedIntegral Φ w k := by
      funext X
      simp only [separatedIntegral, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
    rw [he]
    exact Submodule.smul_mem _ _ (hwS k)

private theorem leftAverage_finite (Φ : 𝓢(Mat, ℂ)) {w : C(U, ℂ)} (hw : w ∈ polynomialStar n) :
    FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℝ n =>
      fun X : Mat => leftAverage Φ w (k.val⁻¹.val * X))) := by
  have hw' : w ∈ (polynomialStar n).toSubalgebra := hw
  rw [polynomialStar_toSubalgebra] at hw'
  obtain ⟨_, S, hS, hs⟩ := separatedIntegral_finite Φ (inv_mul_mem_separated hw')
  let : FiniteDimensional ℂ S := hS
  apply Submodule.finiteDimensional_of_le (S₂ := S)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  let u : U := ⟨k.val.val, k.2⟩
  have hu : u⁻¹.val = k.val⁻¹.val := by
    have hk : Unitary.toUnits u = k.val := Units.ext rfl
    exact congrArg Units.val ((map_inv (Unitary.toUnits : U →* Langlands.GeneralLinear n ℝ) u).trans
      (congrArg Inv.inv hk))
  have he : (fun X : Mat => leftAverage Φ w (k.val⁻¹.val * X)) =
      separatedIntegral Φ (fun u v => w (u⁻¹ * v)) u := by
    funext X
    rw [← hu, leftAverage_apply]
    change _ = ∫ v : U, w (u⁻¹ * v) * Φ (v⁻¹.val * X) ∂Haar
    rw [← integral_mul_left_eq_self (fun v : U => w (u⁻¹ * v) * Φ (v⁻¹.val * X)) u]
    apply integral_congr_ae (ae_of_all _ fun v => ?_)
    change w v * Φ (v⁻¹.val * (u⁻¹.val * X)) = w (u⁻¹ * (u * v)) * Φ ((u * v)⁻¹.val * X)
    rw [inv_mul_cancel_left, mul_inv_rev, Matrix.UnitaryGroup.mul_val, Matrix.mul_assoc]
  change (fun X : Mat => leftAverage Φ w (k.val⁻¹.val * X)) ∈ S
  rw [he]
  exact hs u

variable (n) in
/-- Real square Schwartz functions (operator norm on matrices) with finite left orthogonal
orbit span are dense in Schwartz space. -/
def RealOrthogonalSchwartzDensityStatement : Prop :=
  Dense {Φ : 𝓢(Mat, ℂ) | FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℝ n =>
    fun X : Mat => Φ (k.val⁻¹.val * X)))}

set_option maxHeartbeats 500000 in
theorem realOrthogonalSchwartzDensity : RealOrthogonalSchwartzDensityStatement n := by
  let Ofinite : Set 𝓢(Mat, ℂ) := {Φ | FiniteDimensional ℂ (Submodule.span ℂ
    (range fun k : unitaryCompact ℝ n => fun X : Mat => Φ (k.val⁻¹.val * X)))}
  have hdense : Dense (polynomialStar n : Set C(U, ℂ)) := by
    intro w
    rw [← StarSubalgebra.topologicalClosure_coe,
      ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
        (polynomialStar n) polynomialStar_separatesPoints]
    exact StarSubalgebra.mem_top
  have hcompact {Φ : 𝓢(Mat, ℂ)} (hΦ : HasCompactSupport (Φ : Mat → ℂ)) : Φ ∈ closure Ofinite := by
    have h := mem_closure_average_of_dense Haar leftPullback continuous_leftPullback
      (Classical.choose_spec exists_leftPullback_lower).1 (Classical.choose_spec exists_leftPullback_lower).2
      Φ hΦ leftPullback_one (polynomialStar n : Set C(U, ℂ)) hdense
    change Φ ∈ closure ((leftAverage Φ) '' (polynomialStar n : Set C(U, ℂ))) at h
    exact closure_mono (by
      rintro _ ⟨w, hw, rfl⟩
      exact leftAverage_finite Φ hw) h
  intro Φ
  exact closure_minimal (fun _ h => hcompact h) isClosed_closure
    ((dense_hasCompactSupport_schwartz (E := Mat)) Φ)

/-- A sequence of left orthogonal finite real square tests converges to each Schwartz test. -/
theorem exists_tendsto_realOrthogonalFiniteSchwartz (Φ : 𝓢(Mat, ℂ)) :
    ∃ Ψ : ℕ → 𝓢(Mat, ℂ),
      (∀ j, FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℝ n =>
        fun X : Mat => Ψ j (k.val⁻¹.val * X)))) ∧ Filter.Tendsto Ψ Filter.atTop (𝓝 Φ) :=
  mem_closure_iff_seq_limit.mp (realOrthogonalSchwartzDensity (n := n) Φ)

end Langlands.Global.RankinSelbergGlobal.RealJacquet
