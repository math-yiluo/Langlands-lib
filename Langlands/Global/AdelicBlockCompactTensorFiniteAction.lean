import Langlands.Global.AdelicBlockCompactTensorMap
import Langlands.Representation.Smooth.RenardTensorHomExactnessProof

/-! # Finite translation of scalar sections built from compact tensors -/

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
local notation "Gf" => FiniteAdelicGL F n
local notation "ρ0" => Representation.trivial ℂ (FiniteAdelicGL F n) Ai

variable (ef : FiniteAdelicGL F n → Af →ₗ[ℂ] Vf)
variable (ei : ↥(standardInfiniteCompact F n) → Ai →ₗ[ℂ] Vi)
variable (e : Vf ⊗[ℂ] Vi →ₗ[ℂ] coefficientValues F B S)

local notation "efK" => (fun q : ↥(FiniteAdelicGL.standardIntegral F n) => ef (Subtype.val q))

variable (hcov : ∀ (p : compactIntersection B F) (k : standardCompact F n)
    (m : FullLevi F B) (a : Af) (b : Ai),
  (compactTensorValue F B (coefficientValues F B S) (fun q => ef q.val) ei e
    (⟨p.val.val, p.property⟩ * k) (a ⊗ₜ[ℂ] b)).val m =
    (compactTensorValue F B (coefficientValues F B S) (fun q => ef q.val) ei e
      k (a ⊗ₜ[ℂ] b)).val (m * B.leviProjection (Adeles F) p.val))

variable (ρ : Representation ℂ (FiniteAdelicGL F n) Af)
variable (hr : ∀ (d g : FiniteAdelicGL F n) (a : Af), ef g (ρ d a) = ef (g * d) a)
variable (hl : ∀ (p : AdelicBlockParabolic.Finite F B) (g : FiniteAdelicGL F n)
    (a : Af) (b : Vi) (m : FullLevi F B),
  (e (ef (p.val * g) a ⊗ₜ[ℂ] b)).val m =
    (parabolicHalfCharacter F B (ofFinite F B p) : ℂ) *
      (e (ef g a ⊗ₜ[ℂ] b)).val (m * leviPair F B 1 (B.leviProjection (FiniteAdeles F) p)))

local notation "j" => compactTensorSectionMap F B W efK ei e hcov

private theorem compactCoordinates_finite_translate (k : K) (d : Gf) :
    ∃ (p : AdelicBlockParabolic.Finite F B) (l : K),
      k.val * AdelicGL.ofFinite F n d = (ofFinite F B p).val * l.val ∧
      (standardCompactProductEquiv F n l).1 = (standardCompactProductEquiv F n k).1 ∧
      (standardCompactProductEquiv F n k).2.val * d =
        p.val * (standardCompactProductEquiv F n l).2.val := by
  let z := standardCompactProductEquiv F n k
  obtain ⟨β, κ, h, hb, hk⟩ := exists_finite_iwasawa F n (z.2.val * d)
  let p : AdelicBlockParabolic.Finite F B := ⟨β, B.mem_parabolic_of_isUpperTriangular β hb⟩
  let c : FiniteAdelicGL.standardIntegral F n := ⟨κ, hk⟩
  let l := (standardCompactProductEquiv F n).symm (z.1, c)
  have hl : standardCompactProductEquiv F n l = (z.1, c) :=
    (standardCompactProductEquiv F n).apply_symm_apply _
  have hi := congrArg Prod.fst hl
  refine ⟨p, l, ?_, hi, ?_⟩
  · have hz : k.val = AdelicGL.pair F n z.1.val z.2.val :=
      (AdelicGL.pair_projections F n k.val).symm
    calc
      k.val * AdelicGL.ofFinite F n d = AdelicGL.pair F n z.1.val (z.2.val * d) := by
        rw [hz, AdelicGL.ofFinite_eq_pair, AdelicGL.pair_mul, mul_one]
      _ = (ofFinite F B p).val * l.val := by
        change AdelicGL.pair F n z.1.val (z.2.val * d) =
          AdelicGL.pair F n 1 β * AdelicGL.pair F n z.1.val κ
        rw [AdelicGL.pair_mul, one_mul, h]
  · rw [hl]
    exact h

include hr hl hcov in
/-- Finite right translation on the source is the actual finite right
translation of the corresponding scalar adelic section. -/
def finiteTensorSectionIntertwiner :
    (ρ.tprod ρ0).IntertwiningMap (RealizedSections.finiteAction F B S) where
  toLinearMap := j
  isIntertwining' d := by
    apply TensorProduct.ext'
    intro a b
    apply (compactPictureEquiv F B W).injective
    apply Subtype.ext
    funext k m
    change normalizedSlice F B (j (ρ d a ⊗ₜ[ℂ] b)).val k m =
      normalizedSlice F B (fun x => (j (a ⊗ₜ[ℂ] b)).val (x * AdelicGL.ofFinite F n d)) k m
    obtain ⟨p, l, h, hi, hf⟩ := compactCoordinates_finite_translate F B k d
    rw [normalizedSlice_rightTranslate F B _ _ _ _ _ h,
      normalizedSlice_compactTensorSectionMap, normalizedSlice_compactTensorSectionMap,
      compactTensorValue_tmul, compactTensorValue_tmul]
    rw [hr, hf, hi]
    have hμ : B.leviProjection (Adeles F) (ofFinite F B p) =
        leviPair F B 1 (B.leviProjection (FiniteAdeles F) p) := by
      change B.leviProjection (Adeles F) (pair F B 1 p) = _
      rw [leviProjection_pair, map_one]
    rw [hμ]
    exact hl p (standardCompactProductEquiv F n l).2.val a
      (ei (standardCompactProductEquiv F n k).1 b) m

local instance compactTensorFiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRealizedSections F B S) := Submodule.addCommGroup _

/-- Smoothness of the finite source gives finite-smooth realized sections. -/
def finiteSmoothTensorSectionIntertwiner (hρ : IsSmooth ρ) :
    (ρ.tprod ρ0).IntertwiningMap (finiteSmoothAction F B S) :=
  smoothLift (Renard.Smooth.TensorHom.tensor_smooth ρ ρ0 hρ (fun _ => ⟨⊤, fun _ => rfl⟩))
    (finiteTensorSectionIntertwiner F B S ef ei e hcov ρ hr hl)

end Langlands.Global.AdelicBlockScalarSections
