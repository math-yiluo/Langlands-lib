import Langlands.Global.AdelicBlockCompactTensorFaithfulness
import Langlands.Global.AdelicBlockCompactTensorFiniteAction
import Langlands.Global.AdelicBlockCompactTensorSmooth
import Langlands.Global.AdelicBlockNormalizedCoefficientMap

/-! # Smooth embeddings from compact tensor evaluations -/

noncomputable section

open scoped Classical ContDiff Matrix.Norms.Operator TensorProduct Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

universe u v

namespace Langlands.Global.AdelicBlockScalarSections

open Automorphic GeneralLinear PrimitiveAdelicHeight AdelicBlockParabolic ArchimedeanGL
open AdelicBlockDeterminantCharacter

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable (S : ∀ i, OperatorRealization F (B.size i))
variable {Af Ai Vf Vi : Type v}
variable [AddCommGroup Af] [Module ℂ Af] [AddCommGroup Ai] [Module ℂ Ai]
variable [AddCommGroup Vf] [Module ℂ Vf] [AddCommGroup Vi] [Module ℂ Vi]

local notation "Gf" => FiniteAdelicGL F n
local notation "Kf" => FiniteAdelicGL.standardIntegral F n
local notation "Ki" => standardInfiniteCompact F n
local notation "K" => standardCompact F n
local notation "C" => coefficientValues F B S
local notation "Sections" => smoothCompactFiniteSections F B S

local instance : AddCommGroup (FiniteSmoothRealizedSections F B S) := Submodule.addCommGroup _
local instance : AddCommGroup Sections := Submodule.addCommGroup _

/-- A faithful tensor evaluation in the smooth section carrier, with the two
right translation laws and the normalized compact coefficient formula. -/
structure CompactTensorSmoothEmbedding
    (ρ : Representation ℂ Gf Af) (κ : Representation ℂ Ki Ai)
    (ef : Gf → Af →ₗ[ℂ] Vf) (ei : Ki → Ai →ₗ[ℂ] Vi)
    (e : Vf ⊗[ℂ] Vi →ₗ[ℂ] C) where
  toLinearMap : Af ⊗[ℂ] Ai →ₗ[ℂ] Sections
  map_injective : Function.Injective toLinearMap
  finite_intertwines : ∀ (d : Gf) (x : Af ⊗[ℂ] Ai),
    toLinearMap ((ρ.tprod (Representation.trivial ℂ Gf Ai)) d x) =
      smoothCompactFiniteAction F B S d (toLinearMap x)
  compact_intertwines : ∀ (k : Ki) (x : Af ⊗[ℂ] Ai),
    toLinearMap ((Representation.tprod (Representation.trivial ℂ Ki Af) κ) k x) =
      smoothCompactAction F B S k (toLinearMap x)
  coefficient : ∀ (k : Ki) (l : Kf) (x : Af ⊗[ℂ] Ai),
    normalizedCoefficientMap F B S (compactPair F k l) (toLinearMap x) =
      e (TensorProduct.map (ef l.val) (ei k) x)

/-- Use the finite-smooth lift to place the compact intertwiner in the smooth
section carrier. Its finite translation law and injectivity descend from
the same scalar section map. -/
def compactTensorSmoothEmbedding
    (ρ : Representation ℂ Gf Af) (κ : Representation ℂ Ki Ai)
    (ef : Gf → Af →ₗ[ℂ] Vf) (ei : Ki → Ai →ₗ[ℂ] Vi)
    (e : Vf ⊗[ℂ] Vi →ₗ[ℂ] C)
    (hcov : ∀ (p : compactIntersection B F) (k : K) (m : FullLevi F B) (a : Af) (b : Ai),
      (compactTensorValue F B C (fun q => ef q.val) ei e
        (⟨p.val.val, p.property⟩ * k) (a ⊗ₜ[ℂ] b)).val m =
        (compactTensorValue F B C (fun q => ef q.val) ei e k (a ⊗ₜ[ℂ] b)).val
          (m * B.leviProjection (Adeles F) p.val))
    (hρ : IsSmooth ρ)
    (hfr : ∀ (d g : Gf) (a : Af), ef g (ρ d a) = ef (g * d) a)
    (hfl : ∀ (p : AdelicBlockParabolic.Finite F B) (g : Gf)
        (a : Af) (b : Vi) (m : FullLevi F B),
      (e (ef (p.val * g) a ⊗ₜ[ℂ] b)).val m =
        (parabolicHalfCharacter F B (ofFinite F B p) : ℂ) *
          (e (ef g a ⊗ₜ[ℂ] b)).val (m * leviPair F B 1 (B.leviProjection (FiniteAdeles F) p)))
    (hir : ∀ (d k : Ki) (b : Ai), ei k (κ d b) = ei (k * d) b)
    (hκ : ∀ b : Ai, FiniteVectors.IsFiniteVector κ b)
    (hsmooth : ∀ (a : Af) (b : Ai) (k : Ki) (l : Kf) (m : FullLevi F B),
      ∃ φ : ArchimedeanMatrix F n → ℂ, ContDiffAt ℝ ∞ φ (compactMatrix F k) ∧
        ∀ᶠ x in 𝓝 (compactMatrix F k), ∀ h : Ki, compactMatrix F h = x →
          φ x = (e (ef l.val a ⊗ₜ[ℂ] ei h b)).val m)
    (hf : ∀ a : Af, (∀ l : Kf, ef l.val a = 0) → a = 0)
    (hi : ∀ b : Ai, (∀ k : Ki, ei k b = 0) → b = 0)
    (he : Function.Injective e) :
    CompactTensorSmoothEmbedding F B S ρ κ ef ei e := by
  let efK (q : Kf) := ef q.val
  let Jf := finiteSmoothTensorSectionIntertwiner F B S ef ei e hcov ρ hfr hfl hρ
  have hs (x : Af ⊗[ℂ] Ai) : IsSmoothVector (RealizedSections.finiteAction F B S)
      (compactTensorSectionMap F B C efK ei e hcov x) := (Jf x).property
  let J := smoothCompactTensorSectionIntertwiner F B S efK ei e hcov hsmooth κ hir hs hκ
  refine ⟨J.toLinearMap, ?_, ?_, J.isIntertwining _ _, ?_⟩
  · intro x y hxy
    apply compactTensorSectionMap_injective F B C efK ei e hcov hf hi he
    exact congrArg (fun f : Sections => f.val.val) hxy
  · intro d x
    apply Subtype.ext
    exact Jf.isIntertwining _ _ d x
  · intro k l x
    apply Subtype.ext
    funext m
    let q := compactPair F k l
    have hq : standardCompactProductEquiv F n q = (k, l) := by
      change standardCompactProductEquiv F n ((standardCompactProductEquiv F n).symm (k, l)) = _
      exact (standardCompactProductEquiv F n).apply_symm_apply (k, l)
    change normalizedSlice F B (compactTensorSectionMap F B C efK ei e hcov x).val q m =
      (e (TensorProduct.map (ef l.val) (ei k) x)).val m
    rw [normalizedSlice_compactTensorSectionMap]
    change (e (TensorProduct.map (ef (standardCompactProductEquiv F n q).2.val)
      (ei (standardCompactProductEquiv F n q).1) x)).val m = _
    rw [hq]

end Langlands.Global.AdelicBlockScalarSections
