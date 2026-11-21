import Langlands.Global.AdelicBlockCompactProduct

/-! # Tensor evaluations in the actual adelic compact model -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace Langlands.Global.AdelicBlockScalarSections

open GeneralLinear PrimitiveAdelicHeight AdelicBlockParabolic AdelicBlockDeterminantCharacter

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable (W : Submodule ℂ (FullLevi F B → ℂ))
variable {Af Ai Vf Vi : Type v}
variable [AddCommGroup Af] [Module ℂ Af] [AddCommGroup Ai] [Module ℂ Ai]
variable [AddCommGroup Vf] [Module ℂ Vf] [AddCommGroup Vi] [Module ℂ Vi]

local notation "K" => standardCompact F n
local notation "KI" => standardInfiniteCompact F n
local notation "KF" => FiniteAdelicGL.standardIntegral F n
local notation "H" => compactIntersection B F
local notation "M" => FullLevi F B

variable (ef : ↥(FiniteAdelicGL.standardIntegral F n) → Af →ₗ[ℂ] Vf)
variable (ei : ↥(standardInfiniteCompact F n) → Ai →ₗ[ℂ] Vi)
variable (e : Vf ⊗[ℂ] Vi →ₗ[ℂ] W)

/-- At a compact point, evaluate each factor in its actual coordinate and
map the resulting coefficient tensor into the scalar Levi space. -/
def compactTensorValue (k : K) : Af ⊗[ℂ] Ai →ₗ[ℂ] W := by
  let a : ↥KI × ↥KF := standardCompactProductEquiv F n k
  let f : Af →ₗ[ℂ] Vf := ef a.2
  let g : Ai →ₗ[ℂ] Vi := ei a.1
  exact e.comp (TensorProduct.map f g)

theorem compactTensorValue_tmul (k : K) (a : Af) (b : Ai) :
    compactTensorValue F B W ef ei e k (a ⊗ₜ[ℂ] b) =
      e (ef (standardCompactProductEquiv F n k).2 a ⊗ₜ[ℂ]
        ei (standardCompactProductEquiv F n k).1 b) :=
  congrArg e (TensorProduct.map_tmul _ _ a b)

variable (hcov : ∀ (p : compactIntersection B F) (k : standardCompact F n)
    (m : FullLevi F B) (a : Af) (b : Ai),
  (compactTensorValue F B W ef ei e (⟨p.val.val, p.property⟩ * k) (a ⊗ₜ[ℂ] b)).val m =
    (compactTensorValue F B W ef ei e k (a ⊗ₜ[ℂ] b)).val (m * B.leviProjection (Adeles F) p.val))

include hcov in
private theorem compactTensorValue_covariant (p : Full F B)
    (hp : p.val ∈ standardCompact F n) (k : K) (m : M) (x : Af ⊗[ℂ] Ai) :
    (compactTensorValue F B W ef ei e (⟨p.val, hp⟩ * k) x).val m =
      (parabolicHalfCharacter F B p : ℂ) *
        (compactTensorValue F B W ef ei e k x).val (m * B.leviProjection (Adeles F) p) := by
  rw [parabolicHalfCharacter_eq_one_of_mem_standardCompact B F p hp, Units.val_one, one_mul]
  let L : Af ⊗[ℂ] Ai →ₗ[ℂ] ℂ := (LinearMap.proj m).comp
    (W.subtype.comp (compactTensorValue F B W ef ei e (⟨p.val, hp⟩ * k)))
  let R : Af ⊗[ℂ] Ai →ₗ[ℂ] ℂ := (LinearMap.proj (m * B.leviProjection (Adeles F) p)).comp
    (W.subtype.comp (compactTensorValue F B W ef ei e k))
  have h : L = R := by
    apply TensorProduct.ext'
    intro a b
    change (compactTensorValue F B W ef ei e (⟨p.val, hp⟩ * k) (a ⊗ₜ[ℂ] b)).val m =
      (compactTensorValue F B W ef ei e k (a ⊗ₜ[ℂ] b)).val (m * B.leviProjection (Adeles F) p)
    exact hcov ⟨p, hp⟩ k m a b
  exact LinearMap.congr_fun h x

private def compactTensorSlices : Af ⊗[ℂ] Ai →ₗ[ℂ] CompactSections F B W where
  toFun x := ⟨fun k => (compactTensorValue F B W ef ei e k x).val,
    fun k => (compactTensorValue F B W ef ei e k x).property,
    fun p hp k m => compactTensorValue_covariant F B W ef ei e hcov p hp k m x⟩
  map_add' x y := Subtype.ext (funext fun k =>
    congrArg (fun f : W => f.val) (map_add (compactTensorValue F B W ef ei e k) x y))
  map_smul' z x := Subtype.ext (funext fun k =>
    congrArg (fun f : W => f.val) (map_smul (compactTensorValue F B W ef ei e k) z x))

include ef ei e hcov in
/-- Tensor evaluations with the compact parabolic covariance on pure factors
extend to genuine scalar sections on the full adelic group. -/
def compactTensorSectionMap : Af ⊗[ℂ] Ai →ₗ[ℂ] ScalarSections F B W :=
  (compactPictureEquiv F B W).symm.toLinearMap.comp (compactTensorSlices F B W ef ei e hcov)

@[simp]
theorem normalizedSlice_compactTensorSectionMap (x : Af ⊗[ℂ] Ai) (k : K) (m : M) :
    normalizedSlice F B (compactTensorSectionMap F B W ef ei e hcov x).val k m =
      (compactTensorValue F B W ef ei e k x).val m :=
  congrArg (fun Φ : CompactSections F B W => Φ.val k m)
    ((compactPictureEquiv F B W).apply_symm_apply (compactTensorSlices F B W ef ei e hcov x))

end Langlands.Global.AdelicBlockScalarSections
