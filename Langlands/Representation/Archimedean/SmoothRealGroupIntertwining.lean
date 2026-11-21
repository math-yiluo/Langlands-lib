import Langlands.Representation.Archimedean.SmoothUnitActionDerivative
import Langlands.Representation.Archimedean.RealBlockFourierPropagation

/-! # Integrating the derived intertwining identity for real general linear groups -/

noncomputable section

open Filter Langlands.GeneralLinear
open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.DerivativeSmoothVectors

section Units

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  (R : Aˣ →* (E →L[ℂ] E)) (S : Aˣ →* (F →L[ℂ] F))

local notation "J" => 𝓘(ℝ, A)
local notation "D₁" => DerivativeSmoothVectors J R
local notation "D₂" => DerivativeSmoothVectors J S

omit [FiniteDimensional ℝ A] in
private theorem operator_neg_apply (X : A) (v : D₂) :
    operator J S (-X) v = -(operator J S X v) := by
  apply (toSmooth J S).injective
  change smoothLieDerivativeDirection J S (-X) (toSmooth J S v) =
    -(smoothLieDerivativeDirection J S X (toSmooth J S v))
  rw [map_neg]
  rfl

omit [FiniteDimensional ℝ A] in
private theorem hasDerivAt_inv_value {γ : ℝ → Aˣ} {Y : A} {t : ℝ}
    (hγ : HasDerivAt (fun x => (γ x).val) Y t) :
    HasDerivAt (fun x => (γ x)⁻¹.val) (-((γ t)⁻¹.val * Y * (γ t)⁻¹.val)) t := by
  have h := (hasFDerivAt_ringInverse (𝕜 := ℝ) (γ t)).comp_hasDerivAt t hγ
  simpa only [Function.comp_def, Ring.inverse_unit, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply] using h

private theorem hasDerivAt_continuousLinear_tvs
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
    (T : V →L[ℝ] W) {f : ℝ → V} {v : V} {t : ℝ} (h : HasDerivAt f v t) :
    HasDerivAt (fun s => T (f s)) (T v) t := by
  rw [Langlands.Analysis.hasDerivAt_iff_tendsto_slope_tvs] at h ⊢
  refine (T.continuous.continuousAt.tendsto.comp h).congr fun s => ?_
  simp only [Function.comp_apply, slope_def_module, map_smul, map_sub]

/-- A continuous linear map that commutes with genuine Lie derivatives commutes
with the group action of each point on a differentiable path from the identity. -/
theorem map_representation_of_differentiable_path
    (hR : IsContinuousRepresentation R) (hS : IsContinuousRepresentation S)
    (T : D₁ →L[ℂ] D₂)
    (hT : ∀ X v, T (operator J R X v) = operator J S X (T v))
    (γ : ℝ → Aˣ) (hγ₀ : γ 0 = 1) (hγ : Differentiable ℝ (fun t => (γ t).val))
    (s : ℝ) (v : D₁) : T (representation J R (γ s) v) = representation J S (γ s) (T v) := by
  let w (t : ℝ) : D₂ := T (representation J R (γ t) v)
  let f (t : ℝ) : D₂ := representation J S (γ t)⁻¹ (w t)
  have hd (t : ℝ) : HasDerivAt f 0 t := by
    let g := γ t
    let Y := deriv (fun x => (γ x).val) t
    let X := g⁻¹.val * Y
    let Z := Y * g⁻¹.val
    have h₁ : HasDerivAt (fun x => (γ x).val) Y t := (hγ t).hasDerivAt
    have h₂ := hasDerivAt_unitsChartOrbit R hR g v h₁ rfl
    simp only [unitsChartAction_val] at h₂
    have hw : HasDerivAt w (operator J S Z (w t)) t := by
      have h := hasDerivAt_continuousLinear_tvs (T.restrictScalars ℝ) h₂
      change HasDerivAt w (T (representation J R g (operator J R X v))) t at h
      rw [← show inverseConjugationCLM g Z = X by
        simp only [inverseConjugationCLM_apply, X, Z, mul_assoc]
        rw [show g⁻¹.val * g.val = 1 from g.inv_val, mul_one],
        ← operator_representation_units, hT] at h
      exact h
    have h₃ := hasDerivAt_unitsChartAction S hS (g⁻¹) (hasDerivAt_inv_value h₁) rfl hw
    simp only [unitsChartAction_val] at h₃
    have h₄ : (g⁻¹)⁻¹.val * (-(g⁻¹.val * Y * g⁻¹.val)) = -Z := by
      simp only [inv_inv, mul_neg, Z]
      congr 1
      rw [← mul_assoc, ← mul_assoc, show g.val * g⁻¹.val = 1 from g.val_inv, one_mul]
    rw [h₄, operator_neg_apply, neg_add_cancel, map_zero] at h₃
    exact h₃
  have he (Xs : List A) : derivativeCoordinates J S (f s) Xs = derivativeCoordinates J S (f 0) Xs := by
    let L := (derivativeCLM J S Xs).restrictScalars ℝ
    have dc (t : ℝ) : HasDerivAt (fun x => L (f x)) 0 t := by
      simpa only [map_zero] using hasDerivAt_continuousLinear_tvs L (hd t)
    exact is_const_of_deriv_eq_zero (fun t => (dc t).differentiableAt) (fun t => (dc t).deriv) s 0
  have hconst : f s = f 0 := derivativeCoordinates_injective J S (funext he)
  have hc : representation J S (γ s)⁻¹ (T (representation J R (γ s) v)) = T v := by
    simpa only [f, w, hγ₀, inv_one, map_one, Module.End.one_apply] using hconst
  have h := congrArg (representation J S (γ s)) hc
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] using h

end Units

section RealMatrices

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  {n : ℕ} (R : Langlands.GeneralLinear n ℝ →* (E →L[ℂ] E))
  (S : Langlands.GeneralLinear n ℝ →* (F →L[ℂ] F))

local notation "J" => matrixModel ℝ n
local notation "D₁" => DerivativeSmoothVectors J R
local notation "D₂" => DerivativeSmoothVectors J S

open RealBlockPropagation RealPrincipalSeriesDuality

/-- On the genuine smooth carriers a continuous compact and Lie intertwiner
intertwines the entire real general linear group. -/
theorem map_representation_real_of_compact_and_lie
    (hR : IsContinuousRepresentation R) (hS : IsContinuousRepresentation S)
    (T : D₁ →L[ℂ] D₂)
    (hLie : ∀ X v, T (operator J R X v) = operator J S X (T v))
    (hK : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ) v,
      T (representation J R (Unitary.toUnits k) v) = representation J S (Unitary.toUnits k) (T v))
    (g : Langlands.GeneralLinear n ℝ) (v : D₁) :
    T (representation J R g v) = representation J S g (T v) := by
  obtain ⟨l, u, k, hk, hg⟩ := exists_expDiagonal_mul_upperUnipotent_mul_unitaryCompact g
  let M := u.val.val - (1 : Matrix (Fin n) (Fin n) ℝ)
  have hM : M.IsUpperTriangular := u.property.1.sub Matrix.blockTriangular_one
  have hdiag (i : Fin n) : M i i = 0 := by
    change u.val.val i i - (1 : Matrix (Fin n) (Fin n) ℝ) i i = 0
    rw [u.property.2 i, Matrix.one_apply_eq, sub_self]
  let c (t : ℝ) := matrixExpUnit n (t • Matrix.diagonal l) * (unipotentLine M hM hdiag t).val
  have hcVal (t : ℝ) : (c t).val =
      NormedSpace.exp (t • Matrix.diagonal l) * (1 + t • M) := by
    change (matrixExpUnit n (t • Matrix.diagonal l) * (unipotentLine M hM hdiag t).val).val = _
    rw [Units.val_mul, matrixExpUnit_val, unipotentLine_val]
  have hc₀ : c 0 = 1 := by
    apply Units.ext
    rw [hcVal]
    simp
  have hc₁ : c 1 = matrixExpUnit n (Matrix.diagonal l) * u.val := by
    apply Units.ext
    rw [hcVal, Units.val_mul, matrixExpUnit_val]
    simp [M]
  have hc : Differentiable ℝ (fun t => (c t).val) := by
    simp_rw [hcVal]
    have hExp : Differentiable ℝ (fun t : ℝ => NormedSpace.exp (t • Matrix.diagonal l)) :=
      fun t => (hasDerivAt_exp_smul_const (𝕂 := ℝ) (Matrix.diagonal l) t).differentiableAt
    have hLine : Differentiable ℝ (fun t : ℝ => 1 + t • M) :=
      fun t => (((hasDerivAt_id t).smul_const M).const_add 1).differentiableAt
    exact hExp.mul hLine
  let q : Matrix.unitaryGroup (Fin n) ℝ := ⟨k.val, hk⟩
  have hq : Unitary.toUnits q = k := Units.ext rfl
  have hg' : g = c 1 * Unitary.toUnits q := by rw [hc₁, hq, mul_assoc, hg]
  calc
    _ = T (representation J R (c 1) (representation J R (Unitary.toUnits q) v)) := by
      congr 1
      rw [← Module.End.mul_apply, ← map_mul, ← hg']
    _ = representation J S (c 1) (T (representation J R (Unitary.toUnits q) v)) :=
      map_representation_of_differentiable_path R S hR hS T hLie c hc₀ hc 1 _
    _ = _ := by rw [hK, ← Module.End.mul_apply, ← map_mul, ← hg']

end RealMatrices

universe u₁ u₂

/-- Continuous compact and Lie intertwiners of genuine smooth real general
linear group representations are equivariant for the full group. -/
def SmoothRealGroupIntertwiningStatement : Prop :=
  ∀ (n : ℕ) (E : Type u₁) (F : Type u₂)
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (R : Langlands.GeneralLinear n ℝ →* (E →L[ℂ] E))
    (S : Langlands.GeneralLinear n ℝ →* (F →L[ℂ] F)),
    IsContinuousRepresentation R → IsContinuousRepresentation S →
    let I := matrixModel ℝ n
    ∀ (T : DerivativeSmoothVectors I R →L[ℂ] DerivativeSmoothVectors I S),
      (∀ X v, T (operator I R X v) = operator I S X (T v)) →
      (∀ (k : Matrix.unitaryGroup (Fin n) ℝ) v,
        T (representation I R (Unitary.toUnits k) v) = representation I S (Unitary.toUnits k) (T v)) →
      ∀ g v, T (representation I R g v) = representation I S g (T v)

theorem smoothRealGroupIntertwining : SmoothRealGroupIntertwiningStatement.{u₁,u₂} := by
  intro n E F _ _ _ _ R S hR hS _ T hLie hK
  exact map_representation_real_of_compact_and_lie R S hR hS T hLie hK

end Langlands.Archimedean.DerivativeSmoothVectors
