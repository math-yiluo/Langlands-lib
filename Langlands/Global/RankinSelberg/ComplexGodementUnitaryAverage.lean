import Langlands.Analysis.SchwartzCompactAverage
import Langlands.Global.RankinSelberg.ComplexGodementCompactPairing
import Langlands.Global.RankinSelberg.ComplexGodementKFinite
import Langlands.Representation.Archimedean.UnitaryFinitePolynomial
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-! # Compact-finite averages of full-row-rank Godement tests -/

noncomputable section
open MeasureTheory Set
open scoped Classical Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.UnitaryFinitePolynomial (polynomialStar polynomialStar_toSubalgebra
  separated inv_mul_mem_separated)

local instance godementAverageUnitaryMeasure (m : ℕ) : MeasurableSpace (Matrix.unitaryGroup (Fin m) ℂ) :=
  borel _
local instance godementAverageUnitaryBorel (m : ℕ) : BorelSpace (Matrix.unitaryGroup (Fin m) ℂ) := ⟨rfl⟩

variable {m : ℕ}
local notation "K" => Matrix.unitaryGroup (Fin (m + 1)) ℂ
local notation "Rect" => Matrix (Fin m) (Fin (m + 1)) ℂ
local notation "Square" => Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ
local notation "Test" => 𝓢(Rect, ℂ)
local notation "κ" => compactMatrixHaar (m + 1)

private def rightMatrixAction : Square →ₗ[ℝ] (Rect →L[ℝ] Rect) where
  toFun A := (mulRightLinearMap (Fin m) ℝ A).toContinuousLinearMap
  map_add' A B := by ext X i j; exact congrArg (fun M : Rect => M i j) (Matrix.mul_add X A B)
  map_smul' c A := by ext X i j; exact congrArg (fun M : Rect => M i j) (Matrix.mul_smul X c A)

private def unitaryPullback (k : K) : Rect →L[ℝ] Rect := rightMatrixAction k.val

private theorem continuous_unitaryPullback : Continuous (unitaryPullback (m := m)) :=
  rightMatrixAction.toContinuousLinearMap.continuous.comp continuous_subtype_val

private theorem unitaryPullback_mul_inv (X : Rect) (k : K) : (X * k.val) * k⁻¹.val = X := by
  change (X * (Unitary.toUnits k).val) * (Unitary.toUnits k)⁻¹.val = X
  rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

private theorem exists_unitaryPullback_lower :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : Rect) (k : K), ‖X‖ ≤ C * ‖unitaryPullback k X‖ := by
  have hc := (continuous_unitaryPullback (m := m)).comp (continuous_inv (G := K))
  obtain ⟨B, hB⟩ := (isCompact_univ.image hc.norm).bddAbove
  refine ⟨max B 0, le_max_right _ _, fun X k => ?_⟩
  have hb : ‖unitaryPullback k⁻¹‖ ≤ max B 0 :=
    (hB ⟨k, mem_univ _, rfl⟩).trans (le_max_left _ _)
  calc
    ‖X‖ = ‖unitaryPullback k⁻¹ (unitaryPullback k X)‖ :=
      congrArg norm (unitaryPullback_mul_inv X k).symm
    _ ≤ _ := ((unitaryPullback k⁻¹).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

private def averageBound (m : ℕ) : ℝ := (exists_unitaryPullback_lower (m := m)).choose

private theorem averageBound_spec :
    0 ≤ averageBound m ∧ ∀ (X : Rect) (k : K), ‖X‖ ≤ averageBound m * ‖unitaryPullback k X‖ :=
  (exists_unitaryPullback_lower (m := m)).choose_spec

/-- Average the right translates of a Godement test against a continuous unitary weight. -/
def unitaryAverage (w : C(K, ℂ)) (Φ : Test) : Test :=
  Langlands.Analysis.SchwartzCompactAverage.average w unitaryPullback Φ κ w.continuous
    continuous_unitaryPullback averageBound_spec.1 averageBound_spec.2

@[simp] theorem unitaryAverage_apply (w : C(K, ℂ)) (Φ : Test) (X : Rect) :
    unitaryAverage w Φ X = ∫ k : K, w k * Φ (X * k.val) ∂κ := rfl

/-- The weighted average has compact full-row-rank support when the original test does. -/
theorem unitaryAverage_support (w : C(K, ℂ)) (Φ : Test) (hΦ : HasCompactSupport Φ)
    (hfull : ∀ X ∈ tsupport Φ, HasFullRowRank X) :
    HasCompactSupport (unitaryAverage w Φ) ∧ ∀ X ∈ tsupport (unitaryAverage w Φ), HasFullRowRank X := by
  let A (p : Rect × K) := p.1 * p.2⁻¹.val
  let M := A '' (tsupport Φ ×ˢ (univ : Set K))
  have hM : IsCompact M := (hΦ.prod isCompact_univ).image
    (continuous_fst.matrix_mul (continuous_subtype_val.comp continuous_snd.inv))
  have hs : tsupport (unitaryAverage w Φ) ⊆ M := by
    apply closure_minimal _ hM.isClosed
    intro X hX
    by_contra hn
    apply hX
    rw [unitaryAverage_apply]
    apply integral_eq_zero_of_ae
    refine ae_of_all _ fun k => mul_eq_zero_of_right _ ?_
    by_contra hk
    exact hn ⟨(X * k.val, k), ⟨subset_tsupport _ hk, mem_univ _⟩, unitaryPullback_mul_inv X k⟩
  refine ⟨hM.of_isClosed_subset (isClosed_tsupport _) hs, fun X hX => ?_⟩
  obtain ⟨⟨Y, k⟩, ⟨hY, _⟩, rfl⟩ := hs hX
  obtain ⟨B, hB⟩ := hfull Y hY
  refine ⟨k.val * B, ?_⟩
  change (Y * (Unitary.toUnits k)⁻¹.val) * ((Unitary.toUnits k).val * B) = 1
  rw [← Matrix.mul_assoc, Matrix.mul_assoc Y, Units.inv_mul, Matrix.mul_one, hB]

private theorem separated_average_span (Φ : Test) {v : K → K → ℂ} (hv : v ∈ separated (m + 1)) :
    (∀ q, Continuous (v q)) ∧ ∃ V : Submodule ℂ (Rect → ℂ), FiniteDimensional ℂ V ∧
      ∀ q, (fun X => ∫ k : K, v q k * Φ (X * k.val) ∂κ) ∈ V := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨α, _, β, rfl⟩ := hv
    let f (X : Rect) := ∫ k : K, β k * Φ (X * k.val) ∂κ
    refine ⟨fun q => continuous_const.mul β.continuous, Submodule.span ℂ {f},
      FiniteDimensional.span_of_finite _ (finite_singleton f), fun q => ?_⟩
    have he : (fun X => ∫ k : K, α q * β k * Φ (X * k.val) ∂κ) = α q • f := by
      funext X
      simp only [Pi.smul_apply, smul_eq_mul, f, mul_assoc, integral_const_mul]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_singleton f))
  | zero =>
    refine ⟨fun _ => continuous_const, ⊥, inferInstance, fun q => ?_⟩
    simp only [Pi.zero_apply, zero_mul, integral_zero]; exact zero_mem _
  | add v₁ v₂ _ _ ih₁ ih₂ =>
    obtain ⟨hc₁, V₁, hV₁, h₁⟩ := ih₁
    obtain ⟨hc₂, V₂, hV₂, h₂⟩ := ih₂
    refine ⟨fun q => (hc₁ q).add (hc₂ q), V₁ ⊔ V₂, inferInstance, fun q => ?_⟩
    have he : (fun X => ∫ k : K, (v₁ + v₂) q k * Φ (X * k.val) ∂κ) =
        (fun X => ∫ k : K, v₁ q k * Φ (X * k.val) ∂κ) +
          (fun X => ∫ k : K, v₂ q k * Φ (X * k.val) ∂κ) := by
      funext X
      have hX : Continuous (fun k : K => Φ (X * k.val)) :=
        Φ.continuous.comp (continuous_const.matrix_mul continuous_subtype_val)
      have hi₁ : Integrable (fun k : K => v₁ q k * Φ (X * k.val)) κ :=
        ((hc₁ q).mul hX).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hi₂ : Integrable (fun k : K => v₂ q k * Φ (X * k.val)) κ :=
        ((hc₂ q).mul hX).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      simp only [Pi.add_apply, add_mul]
      exact integral_add hi₁ hi₂
    rw [he]
    exact add_mem ((show V₁ ≤ V₁ ⊔ V₂ from le_sup_left) (h₁ q))
      ((show V₂ ≤ V₁ ⊔ V₂ from le_sup_right) (h₂ q))
  | smul c v _ ih =>
    obtain ⟨hc, V, hV, h⟩ := ih
    refine ⟨fun q => (hc q).const_smul c, V, hV, fun q => ?_⟩
    have he : (fun X => ∫ k : K, (c • v) q k * Φ (X * k.val) ∂κ) =
        c • (fun X => ∫ k : K, v q k * Φ (X * k.val) ∂κ) := by
      funext X
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
    rw [he]
    exact Submodule.smul_mem _ _ (h q)

/-- Polynomial weights give tests with finite right unitary translate span. -/
theorem unitaryAverage_finite {w : C(K, ℂ)} (hw : w ∈ polynomialStar (m + 1)) (Φ : Test) :
    FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℂ (m + 1) =>
      translateTest k.val (unitaryAverage w Φ))) := by
  have hw' : w ∈ (polynomialStar (m + 1)).toSubalgebra := hw
  rw [polynomialStar_toSubalgebra] at hw'
  obtain ⟨_, V, hV, h⟩ := separated_average_span Φ (inv_mul_mem_separated hw')
  apply Submodule.finiteDimensional_of_le (S₂ := V)
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, hg⟩, rfl⟩
  change translateTest g (unitaryAverage w Φ) ∈ V
  let q : K := ⟨g.val, hg⟩
  rw [show g = Unitary.toUnits q from Units.ext rfl]
  have he : translateTest (Unitary.toUnits q) (unitaryAverage w Φ) =
      fun X => ∫ k : K, w (q⁻¹ * k) * Φ (X * k.val) ∂κ := by
    funext X
    rw [translateTest, unitaryAverage_apply, ← integral_mul_left_eq_self
      (fun k : K => w (q⁻¹ * k) * Φ (X * k.val)) q]
    simp only [inv_mul_cancel_left, Matrix.UnitaryGroup.mul_val, Matrix.mul_assoc]
    rfl
  rw [he]
  exact h q

variable (m) in
/-- A polynomially weighted unitary average preserves compact full-rank support and has a
finite right unitary translate span. -/
def ComplexGodementUnitaryAverageStatement : Prop :=
  ∀ (w : C(K, ℂ)), w ∈ polynomialStar (m + 1) → ∀ Φ : Test,
    HasCompactSupport Φ → (∀ X ∈ tsupport Φ, HasFullRowRank X) →
    HasCompactSupport (unitaryAverage w Φ) ∧
      (∀ X ∈ tsupport (unitaryAverage w Φ), HasFullRowRank X) ∧
      FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℂ (m + 1) =>
        translateTest k.val (unitaryAverage w Φ)))

theorem complexGodementUnitaryAverage : ComplexGodementUnitaryAverageStatement m := by
  intro w hw Φ hΦ hfull
  exact ⟨(unitaryAverage_support w Φ hΦ hfull).1,
    (unitaryAverage_support w Φ hΦ hfull).2, unitaryAverage_finite hw Φ⟩

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
