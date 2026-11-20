import Langlands.Global.AdelicBlockCoefficientTensor
import Langlands.Global.AdelicBlockCompactProjection
import Langlands.Representation.Induction.Definitions

/-!
# The compact induction model of scalar block sections

The actual compact parabolic intersection acts on the realized Levi coefficient
space. The scalar compact picture is the corresponding space of covariant
coefficient-valued functions on the standard compact group.
-/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.GeneralLinear
open AdelicBlockParabolic AdelicBlockDeterminantCharacter PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local notation "K" => (standardCompact F n)
local notation "H" => Subgroup.comap (Subgroup.subtype (standardCompact F n)) (B.parabolic (Adeles F))
local notation "M" => FullLevi F B
local notation "μ" => B.leviProjection (Adeles F)
local notation "intoParabolic" =>
  MonoidHom.subgroupComap (Subgroup.subtype (standardCompact F n)) (B.parabolic (Adeles F))
local notation "W" => coefficientValues F B S

private theorem compactLevi_mul_split (m : M) :
    leviPair F B (leviInfinite F B m) 1 * leviPair F B 1 (leviFinite F B m) = m := by
  funext i
  change AdelicGL.pair F (B.size i) (AdelicGL.infinite F (B.size i) (m i)) 1 *
      AdelicGL.pair F (B.size i) 1 (AdelicGL.finite F (B.size i) (m i)) = m i
  rw [AdelicGL.pair_mul, mul_one, one_mul, AdelicGL.pair_projections]

set_option maxHeartbeats 1000000 in
private theorem coefficientValues_rightCompact {φ : M → ℂ} (hφ : φ ∈ W)
    (p : Full F B) (hp : p.val ∈ standardCompact F n) :
    (fun m : M => φ (m * μ p)) ∈ W := by
  rw [← range_coefficientEvaluation F B S] at hφ ⊢
  obtain ⟨t, rfl⟩ := hφ
  let d := leviFinite F B (μ p)
  let k (i : Fin B.length) : standardInfiniteCompact F (B.size i) :=
    ⟨leviInfinite F B (μ p) i,
      ((mem_standardCompact_iff F (B.size i) _).mp
        (leviProjection_mem_standardCompact B F p hp i)).1⟩
  refine ⟨PiTensorProduct.map (fun i => (S i).compactRepresentation (k i))
    (PiTensorProduct.map (fun i => (S i).finiteRepresentation (d i)) t), ?_⟩
  funext m
  rw [coefficientEvaluation_compact F B S, coefficientEvaluation_finite F B S, mul_assoc]
  exact congrArg (fun a : M => coefficientEvaluation F B S t (m * a))
    (compactLevi_mul_split F B (μ p))

/-- The compact parabolic intersection acts on the actual scalar coefficient space
by right translation along the Levi projection. -/
def compactCoefficientSubrepresentation :
    Subrepresentation ((Whittaker.rightTranslation ℂ M).comp
      ((μ).comp intoParabolic)) where
  toSubmodule := W
  apply_mem_toSubmodule h _ hφ :=
    coefficientValues_rightCompact F B S hφ (intoParabolic h) h.val.property

/-- The inducing representation on the scalar coefficient space. -/
abbrev compactCoefficientAction : Representation ℂ H W :=
  (compactCoefficientSubrepresentation F B S).toRepresentation

/-- The two compact pictures are identified pointwise using the actual scalar
coefficient submodule. -/
def compactCoefficientEquiv :
    CompactSections F B W ≃ₗ[ℂ] Induction.EquivariantFunctions H (compactCoefficientAction F B S)
    where
  toFun Φ := ⟨fun k => ⟨Φ.val k, Φ.property.1 k⟩, fun h k => by
    apply Subtype.ext
    funext m
    change Φ.val (h.val * k) m = Φ.val k (m * μ (intoParabolic h))
    have he := Φ.property.2 (intoParabolic h) h.val.property k m
    have hh : (⟨(intoParabolic h).val, h.val.property⟩ : K) = h.val := Subtype.ext rfl
    simpa only [hh, parabolicHalfCharacter_eq_one_of_mem_standardCompact B F (intoParabolic h)
      h.val.property, Units.val_one, one_mul] using he⟩
  invFun Φ := ⟨fun k => (Φ.val k).val, fun k => (Φ.val k).property, fun p hp k m => by
    let h : H := ⟨⟨p.val, hp⟩, p.property⟩
    rw [parabolicHalfCharacter_eq_one_of_mem_standardCompact B F p hp, Units.val_one, one_mul]
    have he := congrArg (fun f : W => f.val m) (Φ.property h k)
    change (Φ.val ((⟨p.val, hp⟩ : K) * k)).val m = (Φ.val k).val (m * μ p) at he
    exact he⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The scalar section carrier is linearly equivalent to actual compact induction
with the realized coefficient space. -/
def compactInductionEquiv :
    RealizedSections F B S ≃ₗ[ℂ] Induction.EquivariantFunctions H (compactCoefficientAction F B S) :=
  (compactPictureEquiv F B W).trans (compactCoefficientEquiv F B S)

@[simp]
theorem compactInductionEquiv_apply (f : RealizedSections F B S) (k : K) (m : M) :
    ((compactInductionEquiv F B S f).val k).val m = normalizedSlice F B f.val k m := rfl

/-- Compact restriction intertwines the actual right translations. -/
def compactInductionRepresentationEquiv :
    (ScalarSections.compactSubrepresentation F B W).toRepresentation.Equiv
      (Induction.equivariantAction H (compactCoefficientAction F B S)) :=
  Representation.Equiv.mk (compactInductionEquiv F B S) fun k => by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext l
    apply Subtype.ext
    funext m
    change (leviHalfCharacter F B m : ℂ)⁻¹ *
        f.val ((B.leviEmbedding (Adeles F) m * l.val) * k.val) =
      (leviHalfCharacter F B m : ℂ)⁻¹ * f.val (B.leviEmbedding (Adeles F) m * (l.val * k.val))
    rw [mul_assoc]

end Langlands.Global.AdelicBlockScalarSections
