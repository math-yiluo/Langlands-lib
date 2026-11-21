import Langlands.Analysis.SchwartzCompactAverageEvaluation
import Langlands.Global.RankinSelberg.RealGodementColumnNonzero
import Langlands.Global.RankinSelberg.RealGodementFiniteCompactTest
import Langlands.Global.RankinSelberg.RealGodementSpanLie
import Langlands.Representation.Archimedean.RealReverseTransfer

/-! # Finite orthogonal orbit tests detect real Godement coefficients -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear
open Langlands.Analysis.SchwartzCompactAverage Langlands.Analysis.SchwartzCompactFamilies
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open OrthogonalFinitePolynomial

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

variable {t : ℕ}
local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "U" => Matrix.unitaryGroup (Fin (t + 2)) ℝ
local notation "K" => unitaryCompact ℝ (t + 2)
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ
local notation "Y" => Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ
local notation "ρ" => rectangularRightRepresentation (m := t + 1)

private def rightMatrixMultiplication : Y →L[ℝ] X →L[ℝ] X :=
  ({ toFun := fun A => (mulRightLinearMap (Fin (t + 1)) ℝ A).toContinuousLinearMap
     map_add' := fun A B => ContinuousLinearMap.ext fun x => Matrix.mul_add x A B
     map_smul' := fun c A => ContinuousLinearMap.ext fun x => Matrix.mul_smul x c A } :
    Y →ₗ[ℝ] X →L[ℝ] X).toContinuousLinearMap

private def orthogonalPullback (k : U) : X →L[ℝ] X := rightMatrixMultiplication k.val

private theorem continuous_orthogonalPullback : Continuous (orthogonalPullback (t := t)) :=
  rightMatrixMultiplication.continuous.comp continuous_subtype_val

private theorem exists_orthogonalPullback_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : X, ∀ k : U, ‖x‖ ≤ B * ‖orthogonalPullback k x‖ := by
  obtain ⟨B, hB⟩ := (isCompact_range (continuous_orthogonalPullback (t := t)).norm).bddAbove
  have hb (k : U) : ‖orthogonalPullback k‖ ≤ B := hB (mem_range_self k)
  refine ⟨B, (norm_nonneg _).trans (hb 1), fun x k => ?_⟩
  have hCancel : orthogonalPullback k⁻¹ (orthogonalPullback k x) = x := by
    change x * (Unitary.toUnits k).val * (Unitary.toUnits k⁻¹).val = x
    rw [map_inv, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have h := (orthogonalPullback k⁻¹).le_opNorm (orthogonalPullback k x)
  rw [hCancel] at h
  exact h.trans (mul_le_mul_of_nonneg_right (hb k⁻¹) (norm_nonneg _))

private def orthogonalAverage (ν : Measure U) [IsFiniteMeasure ν] (Φ : 𝓢(X, ℂ)) :
    C(U, ℂ) →ₗ[ℂ] 𝓢(X, ℂ) where
  toFun κ := average κ orthogonalPullback Φ ν κ.continuous continuous_orthogonalPullback
    (exists_orthogonalPullback_bound (t := t)).choose_spec.1
    (exists_orthogonalPullback_bound (t := t)).choose_spec.2
  map_add' κ κ' := by
    ext x
    simp only [average_apply, add_apply, ContinuousMap.add_apply, add_mul]
    have hCont : Continuous (fun k : U => Φ (orthogonalPullback k x)) :=
      Φ.continuous.comp (continuous_orthogonalPullback.clm_apply continuous_const)
    exact integral_add ((κ.continuous.mul hCont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) ((κ'.continuous.mul hCont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  map_smul' c κ := by
    ext x
    simp only [average_apply, smul_apply, ContinuousMap.smul_apply, RingHom.id_apply,
      smul_eq_mul, mul_assoc, integral_const_mul]

private theorem orthogonalAverage_apply (ν : Measure U) [IsFiniteMeasure ν]
    (Φ : 𝓢(X, ℂ)) (κ : C(U, ℂ)) (x : X) :
    orthogonalAverage ν Φ κ x = ∫ k, κ k * Φ (x * k.val) ∂ν := rfl

private theorem exists_separated_row_span {f : U → U → ℂ} (hf : f ∈ separated (t + 2)) :
    ∃ V : Submodule ℂ C(U, ℂ), FiniteDimensional ℂ V ∧ ∀ k, ∃ w ∈ V, ∀ x, w x = f k x := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨α, _, β, rfl⟩ := hf
    refine ⟨ℂ ∙ β, inferInstance, fun k => ?_⟩
    exact ⟨α k • β, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self β), fun _ => rfl⟩
  | zero => exact ⟨⊥, inferInstance, fun _ => ⟨0, zero_mem _, fun _ => rfl⟩⟩
  | add f g _ _ hf hg =>
    obtain ⟨V, hV, h⟩ := hf
    obtain ⟨W, hW, h'⟩ := hg
    let := hV
    let := hW
    refine ⟨V ⊔ W, inferInstance, fun k => ?_⟩
    obtain ⟨v, hv, he⟩ := h k
    obtain ⟨w, hw, he'⟩ := h' k
    refine ⟨v + w, Submodule.add_mem_sup hv hw, fun x => ?_⟩
    simp only [ContinuousMap.add_apply, Pi.add_apply, he, he']
  | smul c f _ hf =>
    obtain ⟨V, hV, h⟩ := hf
    refine ⟨V, hV, fun k => ?_⟩
    obtain ⟨v, hv, he⟩ := h k
    refine ⟨c • v, V.smul_mem c hv, fun x => ?_⟩
    simp only [ContinuousMap.smul_apply, Pi.smul_apply, he]

private theorem orthogonalAverage_mem_kFinite (ν : Measure U) [ν.IsHaarMeasure]
    (Φ : 𝓢(X, ℂ)) {κ : C(U, ℂ)} (hκ : κ ∈ polynomialStar (t + 2)) :
    orthogonalAverage ν Φ κ ∈ kFiniteVectors ρ K := by
  have hκ' : κ ∈ (polynomialStar (t + 2)).toSubalgebra := hκ
  rw [polynomialStar_toSubalgebra] at hκ'
  obtain ⟨V, hV, hRows⟩ := exists_separated_row_span (inv_mul_mem_separated hκ')
  let := hV
  apply (mem_kFiniteVectors_iff _ _ _).mpr
  apply Submodule.finiteDimensional_of_le (S₂ := V.map (orthogonalAverage ν Φ))
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  let q : U := ⟨k.val.val, k.property⟩
  obtain ⟨w, hw, hEq⟩ := hRows q
  refine ⟨w, hw, ?_⟩
  have hq : Unitary.toUnits q = k.val := RealReverseTransfer.toUnits_mk k.property
  ext x
  rw [orthogonalAverage_apply, rectangularRightRepresentation_apply, orthogonalAverage_apply]
  simp_rw [hEq]
  rw [← integral_mul_left_eq_self (fun u : U => κ (q⁻¹ * u) * Φ (x * u.val)) q]
  simp only [inv_mul_cancel_left, Matrix.UnitaryGroup.mul_val, Matrix.mul_assoc]
  rw [← hq]
  rfl

private theorem godementLeadingFamily_weylLong_eq_columnMellinLinear
    (D : RealQuotientMeasureData t) [D.groupHaar.IsHaarMeasure]
    (a : ℝˣ) (W : G → ℂ)
    (hW : ∀ Xs, RealLocalWhittaker.iteratedRightDerivative t Xs W ∈
      RealLocalWhittaker.regularFunctions t (-a))
    (hGrowth : RealUniformWhittaker.HasUniformDerivativeGrowth W)
    (p : Fin 2) (z : ℂ) (Φ : 𝓢(X, ℂ)) :
    godementLeadingFamily D a Φ W p (weylLong (t + 2) ℝ) z =
      columnMellinLinear D.groupHaar a W hW hGrowth p.val (z + (t : ℂ) / 2) Φ := by
  have hΦ : rectangularTranslate (1 : G) (1 : H) Φ = Φ := by ext x; simp
  unfold godementLeadingFamily godementColumnValue
  rw [weylLong_mul_self, map_one, hΦ, one_mul]
  rfl

/-- A nonzero regular lower coefficient with uniform derivative growth gives a
nonzero leading column value on a compact full-rank test of finite orthogonal orbit. -/
def RealGodementPolynomialTestStatement (t : ℕ) : Prop :=
  ∀ (D : RealQuotientMeasureData t) (a : ℝˣ) (W : Langlands.GeneralLinear (t + 1) ℝ → ℂ),
    (∀ Xs, RealLocalWhittaker.iteratedRightDerivative t Xs W ∈
      RealLocalWhittaker.regularFunctions t (-a)) →
    RealUniformWhittaker.HasUniformDerivativeGrowth W → W ≠ 0 →
    ∀ (p : Fin 2) (z : ℂ),
    ∃ (S : Set (Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ)), IsCompact S ∧
      (∀ x ∈ S, HasFullRowRank x) ∧
      ∃ Φ : 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ), (∀ x ∉ S, Φ x = 0) ∧
        Φ ∈ kFiniteVectors rectangularRightRepresentation (unitaryCompact ℝ (t + 2)) ∧
        godementLeadingFamily D a Φ W p (weylLong (t + 2) ℝ) z ≠ 0

theorem realGodementPolynomialTest : RealGodementPolynomialTestStatement t := by
  intro D a W hReg hGrowth hW p z
  have hCont : Continuous W := (hReg []).2.1.continuous
  obtain ⟨S, hS, hRank, Φ, hΦ, hNZ⟩ := realGodementColumnNonzero D a W hCont hW p z
  let τ (v : X × U) : X := v.1 * (v.2⁻¹ : U).val
  let T := τ '' (S ×ˢ (univ : Set U))
  have hT : IsCompact T := (hS.prod isCompact_univ).image
    (continuous_fst.matrix_mul (continuous_subtype_val.comp continuous_snd.inv))
  have hRankT (x : X) (hx : x ∈ T) : HasFullRowRank x := by
    obtain ⟨⟨y, k⟩, ⟨hy, _⟩, rfl⟩ := hx
    obtain ⟨R, hR⟩ := hRank y hy
    refine ⟨k.val * R, ?_⟩
    change (y * (Unitary.toUnits k⁻¹).val) * ((Unitary.toUnits k).val * R) = 1
    rw [map_inv, Matrix.mul_assoc y, ← Matrix.mul_assoc ((Unitary.toUnits k)⁻¹).val,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, hR]
  have hSupp (k : U) (x : X) (hx : x ∉ T) : Φ (x * k.val) = 0 := by
    apply hΦ
    intro h
    apply hx
    refine ⟨(x * k.val, k), ⟨h, mem_univ _⟩, ?_⟩
    change x * (Unitary.toUnits k).val * (Unitary.toUnits k⁻¹).val = x
    rw [map_inv, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  let Q (k : U) : supportedSchwartz T :=
    ⟨ρ (Unitary.toUnits k) Φ, fun x hx => by
      rw [rectangularRightRepresentation_apply]
      exact hSupp k x hx⟩
  have hQ (k : U) (x : X) : (Q k).val x = Φ (orthogonalPullback k x) := by
    change (ρ (Unitary.toUnits k) Φ) x = _
    rw [rectangularRightRepresentation_apply]
    rfl
  let ν : Measure U := Measure.haar
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let s := z + (t : ℂ) / 2
  let L₀ := columnMellinLinear D.groupHaar a W hReg hGrowth p.val s
  let L := L₀.comp (supportedSchwartz T).subtype
  obtain ⟨q, hq, hBound⟩ := exists_columnMellinLinear_bound D.groupHaar a W hReg hGrowth p.val s
  let B := exists_orthogonalPullback_bound (t := t)
  obtain ⟨hEval, hAvg⟩ := schwartzCompactAverageEvaluation U ν X X T hT L q hq
    (fun f => hBound f.val) orthogonalPullback continuous_orthogonalPullback B.choose
    B.choose_spec.1 B.choose_spec.2 Φ Q hQ
  let F : C(U, ℂ) := ⟨fun k => L (Q k), hEval⟩
  have hF₁ : F 1 = godementLeadingFamily D a Φ W p (weylLong (t + 2) ℝ) z := by
    rw [godementLeadingFamily_weylLong_eq_columnMellinLinear D a W hReg hGrowth]
    change L₀ (ρ (Unitary.toUnits (1 : U)) Φ) = L₀ Φ
    simp
  have hF : F ≠ 0 := fun h => hNZ (hF₁.symm.trans (congrArg (fun f : C(U, ℂ) => f 1) h))
  obtain ⟨κ, hκ, hnz⟩ : ∃ κ ∈ polynomialStar (t + 2), (∫ k, κ k * F k ∂ν) ≠ 0 := by
    by_contra! h
    exact hF (eq_zero_of_integral_polynomial_mul_eq_zero ν F h)
  let Ψ := supportedAverage ν κ κ.continuous orthogonalPullback continuous_orthogonalPullback
    B.choose_spec.1 B.choose_spec.2 Φ T Q hQ
  have hΨ : Ψ.val = orthogonalAverage ν Φ κ := rfl
  refine ⟨T, hT, hRankT, Ψ.val, Ψ.property, ?_, ?_⟩
  · rw [hΨ]
    exact orthogonalAverage_mem_kFinite ν Φ hκ
  · rw [godementLeadingFamily_weylLong_eq_columnMellinLinear D a W hReg hGrowth]
    change L Ψ ≠ 0
    rw [hAvg κ κ.continuous]
    exact hnz

end Langlands.Global.RankinSelbergGlobal.RealGodement
