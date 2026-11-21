import Langlands.Global.AdelicBlockCompactTensorMap
import Langlands.Representation.Classification.LeftCuspidalDerivative.Criterion

/-! # Faithfulness of the adelic compact tensor section map -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

namespace Langlands.Global.AdelicBlockScalarSections

open GeneralLinear PrimitiveAdelicHeight AdelicBlockParabolic
open Classification.LeftCuspidalDerivative (exists_dual_lid_rTensor_ne_zero)

private theorem tensorRightEvaluations_eq_zero
    {X : Type w} {A B V : Type v}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup V] [Module ℂ V]
    (ev : X → B →ₗ[ℂ] V) (hsep : ∀ y : B, (∀ x, ev x y = 0) → y = 0)
    (w : A ⊗[ℂ] B) (hw : ∀ x, TensorProduct.map LinearMap.id (ev x) w = 0) :
    w = 0 := by
  by_contra hn
  obtain ⟨φ, hφ⟩ := exists_dual_lid_rTensor_ne_zero hn
  apply hφ
  apply hsep
  intro x
  let L := (ev x).comp ((TensorProduct.lid ℂ B).toLinearMap.comp (φ.rTensor B))
  let R := (TensorProduct.lid ℂ V).toLinearMap.comp
    ((φ.rTensor V).comp (TensorProduct.map LinearMap.id (ev x)))
  have he : L = R := by
    apply TensorProduct.ext'
    intro a b
    change ev x (TensorProduct.lid ℂ B (φ.rTensor B (a ⊗ₜ[ℂ] b))) =
      TensorProduct.lid ℂ V (φ.rTensor V (TensorProduct.map LinearMap.id (ev x) (a ⊗ₜ[ℂ] b)))
    rw [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.rTensor_tmul,
      LinearMap.rTensor_tmul, TensorProduct.lid_tmul, TensorProduct.lid_tmul, map_smul]
  change L w = 0
  rw [he]
  change TensorProduct.lid ℂ V (φ.rTensor V (TensorProduct.map LinearMap.id (ev x) w)) = 0
  rw [hw x, map_zero, map_zero]

private theorem tensorEvaluations_eq_zero
    {X Y : Type w} {Af Ai Vf Vi : Type v}
    [AddCommGroup Af] [Module ℂ Af] [AddCommGroup Ai] [Module ℂ Ai]
    [AddCommGroup Vf] [Module ℂ Vf] [AddCommGroup Vi] [Module ℂ Vi]
    (ef : X → Af →ₗ[ℂ] Vf) (ei : Y → Ai →ₗ[ℂ] Vi)
    (hf : ∀ a : Af, (∀ x, ef x a = 0) → a = 0)
    (hi : ∀ b : Ai, (∀ y, ei y b = 0) → b = 0)
    (w : Af ⊗[ℂ] Ai) (hw : ∀ x y, TensorProduct.map (ef x) (ei y) w = 0) :
    w = 0 := by
  have hF (x : X) : TensorProduct.map (ef x) LinearMap.id w = 0 := by
    apply tensorRightEvaluations_eq_zero ei hi
    intro y
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id]
    exact hw x y
  apply (TensorProduct.comm ℂ Af Ai).injective
  rw [map_zero]
  apply tensorRightEvaluations_eq_zero ef hf
  intro x
  rw [TensorProduct.map_comm, hF x, map_zero]

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable (W : Submodule ℂ (FullLevi F B → ℂ))
variable {Af Ai Vf Vi : Type v}
variable [AddCommGroup Af] [Module ℂ Af] [AddCommGroup Ai] [Module ℂ Ai]
variable [AddCommGroup Vf] [Module ℂ Vf] [AddCommGroup Vi] [Module ℂ Vi]

variable (ef : ↥(FiniteAdelicGL.standardIntegral F n) → Af →ₗ[ℂ] Vf)
variable (ei : ↥(standardInfiniteCompact F n) → Ai →ₗ[ℂ] Vi)
variable (e : Vf ⊗[ℂ] Vi →ₗ[ℂ] W)
variable (hcov : ∀ (p : compactIntersection B F) (k : standardCompact F n)
    (m : FullLevi F B) (a : Af) (b : Ai),
  (compactTensorValue F B W ef ei e (⟨p.val.val, p.property⟩ * k) (a ⊗ₜ[ℂ] b)).val m =
    (compactTensorValue F B W ef ei e k (a ⊗ₜ[ℂ] b)).val (m * B.leviProjection (Adeles F) p.val))

/-- Faithful evaluation in each compact factor gives an injective map into
actual scalar adelic sections when the coefficient map is injective. -/
theorem compactTensorSectionMap_injective
    (hf : ∀ a : Af, (∀ x, ef x a = 0) → a = 0)
    (hi : ∀ b : Ai, (∀ y, ei y b = 0) → b = 0) (he : Function.Injective e) :
    Function.Injective (compactTensorSectionMap F B W ef ei e hcov) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro w hw
  apply tensorEvaluations_eq_zero ef ei hf hi w
  intro x y
  let k := (standardCompactProductEquiv F n).symm (y, x)
  have hk : standardCompactProductEquiv F n k = (y, x) :=
    (standardCompactProductEquiv F n).apply_symm_apply _
  have ht : compactTensorValue F B W ef ei e k w = 0 := by
    apply Subtype.ext
    funext m
    have hval := normalizedSlice_compactTensorSectionMap F B W ef ei e hcov w k m
    rw [hw] at hval
    exact hval.symm.trans (by simp [normalizedSlice])
  apply (injective_iff_map_eq_zero e).mp he
  change e (TensorProduct.map (ef (standardCompactProductEquiv F n k).2)
    (ei (standardCompactProductEquiv F n k).1) w) = 0 at ht
  rwa [hk] at ht

/-- The tensor source is equivalent to its realized scalar section image. -/
def compactTensorSectionRangeEquiv
    (hf : ∀ a : Af, (∀ x, ef x a = 0) → a = 0)
    (hi : ∀ b : Ai, (∀ y, ei y b = 0) → b = 0) (he : Function.Injective e) :
    (Af ⊗[ℂ] Ai) ≃ₗ[ℂ] LinearMap.range (compactTensorSectionMap F B W ef ei e hcov) :=
  LinearEquiv.ofInjective _ (compactTensorSectionMap_injective F B W ef ei e hcov hf hi he)

end Langlands.Global.AdelicBlockScalarSections
