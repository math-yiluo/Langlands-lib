import Langlands.Global.AdelicBlockCompactTensorCompactAction
import Langlands.Global.AdelicBlockScalarLieAction

/-! # Smooth scalar sections from compact tensor evaluations -/

noncomputable section

open scoped Classical ContDiff Matrix.Norms.Operator TensorProduct Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace Langlands.Global.AdelicBlockScalarSections

open Automorphic GeneralLinear PrimitiveAdelicHeight AdelicBlockParabolic ArchimedeanGL

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))
variable {Af Ai Vf Vi : Type v}
variable [AddCommGroup Af] [Module ℂ Af] [AddCommGroup Ai] [Module ℂ Ai]
variable [AddCommGroup Vf] [Module ℂ Vf] [AddCommGroup Vi] [Module ℂ Vi]

variable (ef : ↥(FiniteAdelicGL.standardIntegral F n) → Af →ₗ[ℂ] Vf)
variable (ei : ↥(standardInfiniteCompact F n) → Ai →ₗ[ℂ] Vi)
variable (e : Vf ⊗[ℂ] Vi →ₗ[ℂ] coefficientValues F B S)
variable (hcov : ∀ (p : compactIntersection B F) (k : standardCompact F n)
    (m : FullLevi F B) (a : Af) (b : Ai),
  (compactTensorValue F B (coefficientValues F B S) ef ei e
    (⟨p.val.val, p.property⟩ * k) (a ⊗ₜ[ℂ] b)).val m =
    (compactTensorValue F B (coefficientValues F B S) ef ei e
      k (a ⊗ₜ[ℂ] b)).val (m * B.leviProjection (Adeles F) p.val))
variable (hsmooth : ∀ (a : Af) (b : Ai) (k : standardInfiniteCompact F n)
    (l : FiniteAdelicGL.standardIntegral F n) (m : FullLevi F B),
  ∃ φ : ArchimedeanMatrix F n → ℂ, ContDiffAt ℝ ∞ φ (compactMatrix F k) ∧
    ∀ᶠ x in 𝓝 (compactMatrix F k), ∀ h : standardInfiniteCompact F n, compactMatrix F h = x →
      φ x = (e (ef l a ⊗ₜ[ℂ] ei h b)).val m)

local notation "j" => compactTensorSectionMap F B (coefficientValues F B S) ef ei e hcov

include hsmooth in
/-- Local smooth scalar extensions of the compact evaluations of pure tensors
give smooth compact slices for every tensor section. -/
theorem hasSmoothCompactSlices_compactTensorSectionMap (t : Af ⊗[ℂ] Ai) :
    HasSmoothCompactSlices F B S (j t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    intro k l m
    obtain ⟨φ, hφ, he⟩ := hsmooth a b k l m
    refine ⟨φ, hφ, he.mono ?_⟩
    intro x hx h hh
    have hpair : standardCompactProductEquiv F n (compactPair F h l) = (h, l) := by
      change standardCompactProductEquiv F n ((standardCompactProductEquiv F n).symm (h, l)) = _
      exact (standardCompactProductEquiv F n).apply_symm_apply _
    rw [normalizedSlice_compactTensorSectionMap, compactTensorValue_tmul, hpair]
    exact hx h hh
  | add t s ht hs =>
    intro k l m
    obtain ⟨φ, hφ, heφ⟩ := ht k l m
    obtain ⟨ψ, hψ, heψ⟩ := hs k l m
    refine ⟨φ + ψ, hφ.add hψ, ?_⟩
    filter_upwards [heφ, heψ] with x hφx hψx h hh
    rw [Pi.add_apply, hφx h hh, hψx h hh, map_add]
    simp only [normalizedSlice, Submodule.coe_add, Pi.add_apply, mul_add]

variable (κ : Representation ℂ (standardInfiniteCompact F n) Ai)
variable (hr : ∀ (l k : standardInfiniteCompact F n) (b : Ai), ei k (κ l b) = ei (k * l) b)
variable (hs : ∀ x : Af ⊗[ℂ] Ai,
  IsSmoothVector (RealizedSections.finiteAction F B S)
    (compactTensorSectionMap F B (coefficientValues F B S) ef ei e hcov x))
variable (hκ : ∀ b : Ai, FiniteVectors.IsFiniteVector κ b)

local notation "κ0" => Representation.trivial ℂ (standardInfiniteCompact F n) Af
local notation "V" => FiniteSmoothRealizedSections F B S
local notation "W" => smoothCompactFiniteSections F B S

local instance compactTensorSmoothFiniteGroup : AddCommGroup V := Submodule.addCommGroup _

/-- The compact intertwiner lands in the scalar carrier of smooth
compact-finite sections when the pure evaluations admit smooth extensions. -/
def smoothCompactTensorSectionIntertwiner :
    (Representation.tprod κ0 κ).IntertwiningMap (smoothCompactAction F B S) := by
  let I := compactFiniteTensorSectionIntertwiner F B S ef ei e hcov κ hr hs hκ
  let L := (CompactFiniteRealizedSections F B S).subtype.comp I.toLinearMap
  refine ⟨L.codRestrict W (fun t => ?_), fun k => ?_⟩
  · apply (mem_smoothCompactFiniteSections_iff_compactSlices F B S (I t)).mpr
    exact hasSmoothCompactSlices_compactTensorSectionMap F B S ef ei e hcov hsmooth t
  · apply LinearMap.ext
    intro t
    apply Subtype.ext
    change (I (Representation.tprod κ0 κ k t)).val =
      finiteSmoothCompactAction F B S k (I t).val
    exact congrArg (fun x : CompactFiniteRealizedSections F B S => x.val)
      (Representation.IntertwiningMap.isIntertwining _ _ I k t)

end Langlands.Global.AdelicBlockScalarSections
