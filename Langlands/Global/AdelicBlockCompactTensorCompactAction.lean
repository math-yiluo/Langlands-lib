import Langlands.Global.AdelicBlockCompactTensorMap

/-! # Infinite compact translation of scalar sections built from compact tensors -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace Langlands.Global.AdelicBlockScalarSections

open Automorphic GeneralLinear PrimitiveAdelicHeight AdelicBlockParabolic
open AdelicBlockDeterminantCharacter

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))
variable {Af Ai Vf Vi : Type v}
variable [AddCommGroup Af] [Module ℂ Af] [AddCommGroup Ai] [Module ℂ Ai]
variable [AddCommGroup Vf] [Module ℂ Vf] [AddCommGroup Vi] [Module ℂ Vi]

local notation "W" => coefficientValues F B S
local notation "K" => standardCompact F n
local notation "KI" => standardInfiniteCompact F n
local notation "κ0" => Representation.trivial ℂ (standardInfiniteCompact F n) Af

variable (ef : ↥(FiniteAdelicGL.standardIntegral F n) → Af →ₗ[ℂ] Vf)
variable (ei : ↥(standardInfiniteCompact F n) → Ai →ₗ[ℂ] Vi)
variable (e : Vf ⊗[ℂ] Vi →ₗ[ℂ] coefficientValues F B S)
variable (hcov : ∀ (p : compactIntersection B F) (k : standardCompact F n)
    (m : FullLevi F B) (a : Af) (b : Ai),
  (compactTensorValue F B (coefficientValues F B S) ef ei e
    (⟨p.val.val, p.property⟩ * k) (a ⊗ₜ[ℂ] b)).val m =
    (compactTensorValue F B (coefficientValues F B S) ef ei e
      k (a ⊗ₜ[ℂ] b)).val (m * B.leviProjection (Adeles F) p.val))

variable (κ : Representation ℂ (standardInfiniteCompact F n) Ai)
variable (hr : ∀ (l k : standardInfiniteCompact F n) (b : Ai), ei k (κ l b) = ei (k * l) b)

local notation "j" => compactTensorSectionMap F B W ef ei e hcov

private theorem compactCoordinates_mul_infinite (k : K) (l : KI) :
    standardCompactProductEquiv F n (k * infiniteCompactInclusion F l) =
      ((standardCompactProductEquiv F n k).1 * l, (standardCompactProductEquiv F n k).2) := by
  have h : standardCompactProductEquiv F n (infiniteCompactInclusion F l) = (l, 1) := by
    apply Prod.ext
    · apply Subtype.ext
      change AdelicGL.infinite F n (AdelicGL.ofInfinite F n l.val) = l.val
      rw [AdelicGL.ofInfinite_eq_pair, AdelicGL.infinite_pair]
    · apply Subtype.ext
      change AdelicGL.finite F n (AdelicGL.ofInfinite F n l.val) = 1
      rw [AdelicGL.ofInfinite_eq_pair, AdelicGL.finite_pair]
  rw [map_mul, h, Prod.mk_mul_mk, mul_one]

include hr hcov in
/-- Infinite compact translation of the source tensor agrees with actual
infinite compact right translation of its scalar section. -/
def compactTensorSectionIntertwiner :
    (Representation.tprod κ0 κ).IntertwiningMap (RealizedSections.infiniteCompactAction F B S) where
  toLinearMap := j
  isIntertwining' l := by
    apply TensorProduct.ext'
    intro a b
    apply (compactPictureEquiv F B W).injective
    apply Subtype.ext
    funext k m
    change normalizedSlice F B (j (a ⊗ₜ[ℂ] κ l b)).val k m =
      normalizedSlice F B (fun x => (j (a ⊗ₜ[ℂ] b)).val (x * AdelicGL.ofInfinite F n l.val)) k m
    have h : normalizedSlice F B
          (fun x => (j (a ⊗ₜ[ℂ] b)).val (x * AdelicGL.ofInfinite F n l.val)) k m =
        normalizedSlice F B (j (a ⊗ₜ[ℂ] b)).val (k * infiniteCompactInclusion F l) m := by
      exact congrArg (fun x : AdelicGL F n => (leviHalfCharacter F B m : ℂ)⁻¹ *
        (j (a ⊗ₜ[ℂ] b)).val x)
        (mul_assoc (B.leviEmbedding (Adeles F) m) k.val (AdelicGL.ofInfinite F n l.val))
    rw [h, normalizedSlice_compactTensorSectionMap, normalizedSlice_compactTensorSectionMap,
      compactTensorValue_tmul, compactTensorValue_tmul,
      compactCoordinates_mul_infinite F k l, hr]

variable (hs : ∀ x : Af ⊗[ℂ] Ai,
  IsSmoothVector (RealizedSections.finiteAction F B S)
    (compactTensorSectionMap F B (coefficientValues F B S) ef ei e hcov x))

local instance compactTensorCompactActionFiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRealizedSections F B S) := Submodule.addCommGroup _

include hs hr hcov in
/-- The infinite compact intertwiner respects the carrier with an open finite
stabilizer whenever its values belong to that carrier. -/
def compactTensorFiniteSmoothIntertwiner :
    (Representation.tprod κ0 κ).IntertwiningMap (finiteSmoothCompactAction F B S) where
  toLinearMap := LinearMap.codRestrict (smoothVectors (RealizedSections.finiteAction F B S)) j hs
  isIntertwining' k := LinearMap.ext fun x => Subtype.ext
    (Representation.IntertwiningMap.isIntertwining _ _
      (compactTensorSectionIntertwiner F B S ef ei e hcov κ hr) k x)

omit [NumberField F] in
private theorem isFiniteVector_trivial_tprod
    (hκ : ∀ b : Ai, FiniteVectors.IsFiniteVector κ b) (x : Af ⊗[ℂ] Ai) :
    FiniteVectors.IsFiniteVector (Representation.tprod κ0 κ) x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    let l : κ.IntertwiningMap (Representation.tprod κ0 κ) :=
      ⟨TensorProduct.mk ℂ Af Ai a, fun _ => LinearMap.ext fun _ => rfl⟩
    exact (hκ b).map l
  | add x y hx hy => exact hx.add hy

local instance compactTensorCompactActionCompactFiniteGroup :
    AddCommGroup (CompactFiniteRealizedSections F B S) := Submodule.addCommGroup _

/-- If the infinite source is compact-finite, the scalar section map has
compact-finite image in the finite-smooth carrier. -/
def compactFiniteTensorSectionIntertwiner (hκ : ∀ b : Ai, FiniteVectors.IsFiniteVector κ b) :
    (Representation.tprod κ0 κ).IntertwiningMap (compactFiniteSubrepresentation F B S).toRepresentation where
  toLinearMap := (compactTensorFiniteSmoothIntertwiner F B S ef ei e hcov κ hr hs).toLinearMap.codRestrict
    (CompactFiniteRealizedSections F B S) (fun x =>
      (isFiniteVector_trivial_tprod F κ hκ x).map
        (compactTensorFiniteSmoothIntertwiner F B S ef ei e hcov κ hr hs))
  isIntertwining' k := LinearMap.ext fun x => Subtype.ext
    (Representation.IntertwiningMap.isIntertwining _ _
      (compactTensorFiniteSmoothIntertwiner F B S ef ei e hcov κ hr hs) k x)

end Langlands.Global.AdelicBlockScalarSections
