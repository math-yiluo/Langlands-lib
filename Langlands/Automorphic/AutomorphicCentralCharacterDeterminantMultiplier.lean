import Langlands.Automorphic.OperatorDeterminantTwist
import Langlands.Automorphic.CentralCharacterDeterminantMultiplier

/-! # Central-character transport on actual automorphic determinant twists -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

local instance automorphicCentralMultiplierRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance automorphicCentralMultiplierContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance automorphicCentralMultiplierFiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance automorphicCentralMultiplierFormGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance automorphicCentralMultiplierStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance automorphicCentralMultiplierCharacterFormGroup (ω : HeckeCharacter F) :
    AddCommGroup (CentralCharacterAutomorphicForms F n ω) := Submodule.addCommGroup _

private theorem centralCharacterAutomorphic_map_determinantMultiplier
    (χ ω : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (centralCharacterAutomorphicSubrepresentation F n ω).toSubmodule.map
        (AutomorphicForms.finiteOrderDeterminantMultiplier n χ hχ).toLinearMap =
      (centralCharacterAutomorphicSubrepresentation F n (χ ^ n * ω)).toSubmodule := by
  ext f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact centralCharacter_determinantMultiplier n χ ω hg
  · intro hf
    have hg := centralCharacter_determinantMultiplier n χ⁻¹ (χ ^ n * ω) hf
    have hi : (χ⁻¹) ^ n * (χ ^ n * ω) = ω := by
      rw [inv_pow]
      exact inv_mul_cancel_left (χ ^ n) ω
    rw [hi] at hg
    refine ⟨AutomorphicForms.finiteOrderDeterminantMultiplier n χ⁻¹ hχ.inv f, hg, ?_⟩
    apply automorphicToContinuous_injective F n
    change determinantMul n χ (determinantMul n χ⁻¹ (automorphicToContinuous F n f)) =
      automorphicToContinuous F n f
    simpa only [inv_inv (G := HeckeCharacter F)] using
      determinantMul_inv_apply n χ⁻¹ (automorphicToContinuous F n f)

namespace CentralCharacterAutomorphicForms

/-- Actual finite-order multiplication transports the specified automorphic central character. -/
def finiteOrderDeterminantMultiplier (χ ω : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    CentralCharacterAutomorphicForms F n ω ≃L[ℂ]
      CentralCharacterAutomorphicForms F n (χ ^ n * ω) :=
  (AutomorphicForms.finiteOrderDeterminantMultiplier n χ hχ).ofSubmodules _ _
    (centralCharacterAutomorphic_map_determinantMultiplier n χ ω hχ)

@[simp]
theorem evaluate_finiteOrderDeterminantMultiplier
    (χ ω : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (f : CentralCharacterAutomorphicForms F n ω) (g : AdelicGL F n) :
    evaluate F n
        (automorphicToContinuous F n (finiteOrderDeterminantMultiplier n χ ω hχ f).val) g =
      (χ.adelicDeterminant n g : ℂ) *
        evaluate F n (automorphicToContinuous F n f.val) g := rfl

@[simp]
theorem evaluate_finiteOrderDeterminantMultiplier_symm
    (χ ω : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (f : CentralCharacterAutomorphicForms F n (χ ^ n * ω)) (g : AdelicGL F n) :
    evaluate F n
        (automorphicToContinuous F n ((finiteOrderDeterminantMultiplier n χ ω hχ).symm f).val) g =
      ((χ.adelicDeterminant n g)⁻¹ : ℂˣ) *
        evaluate F n (automorphicToContinuous F n f.val) g := rfl

theorem finiteRightAction_determinantMultiplier
    (χ ω : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (d : FiniteAdelicGL F n)
    (f : CentralCharacterAutomorphicForms F n ω) :
    centralCharacterAutomorphicFiniteRightAction F n (χ ^ n * ω) d
        (finiteOrderDeterminantMultiplier n χ ω hχ f) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) •
        finiteOrderDeterminantMultiplier n χ ω hχ
          (centralCharacterAutomorphicFiniteRightAction F n ω d f) := by
  apply Subtype.ext
  exact AutomorphicForms.finiteRightAction_determinantMultiplier n χ hχ d f.val

end CentralCharacterAutomorphicForms

namespace OperatorRealization

variable {n} (S : OperatorRealization F n) (χ ω : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

local instance automorphicCentralMultiplierSpaceGroup :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-- A prescribed central character of an actual full realization transforms by `χ^n`. -/
theorem determinantTwist_hasCentralCharacter
    (hS : S.HasCentralCharacter ω) :
    (S.determinantTwist χ hχ).HasCentralCharacter (χ ^ n * ω) := by
  apply ((S.determinantTwist χ hχ).hasCentralCharacter_iff _).mpr
  intro f
  obtain ⟨g, rfl⟩ := (S.determinantTwistEquiv χ hχ).surjective f
  exact centralCharacter_determinantMultiplier n χ ω ((S.hasCentralCharacter_iff ω).mp hS g)

/-- Actual multiplication also reflects the transformed central-character condition. -/
theorem determinantTwist_hasCentralCharacter_iff :
    (S.determinantTwist χ hχ).HasCentralCharacter (χ ^ n * ω) ↔
      S.HasCentralCharacter ω := by
  constructor
  · intro ht
    apply (S.hasCentralCharacter_iff ω).mpr
    intro f
    have hf := ((S.determinantTwist χ hχ).hasCentralCharacter_iff _).mp ht
      (S.determinantTwistEquiv χ hχ f)
    have hi : (χ⁻¹) ^ n * (χ ^ n * ω) = ω := by
      rw [inv_pow]
      exact inv_mul_cancel_left (χ ^ n) ω
    have hp := centralCharacter_determinantMultiplier n χ⁻¹ (χ ^ n * ω) hf
    change determinantMul n χ⁻¹ (determinantMul n χ (S.toContinuous f)) ∈
      centralCharacterSubrepresentation F n ((χ⁻¹) ^ n * (χ ^ n * ω)) at hp
    rw [determinantMul_inv_apply, hi] at hp
    exact hp
  · exact S.determinantTwist_hasCentralCharacter χ ω hχ

end OperatorRealization

section Cuspidal

variable [CompactSpace (AdeleQuotient F)]

local instance automorphicCentralMultiplierCharacterCuspGroup (ω : HeckeCharacter F) :
    AddCommGroup (CentralCharacterCuspidalForms F n ω) := Submodule.addCommGroup _

private theorem centralCharacterCuspidal_map_determinantMultiplier
    (χ ω : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (centralCharacterCuspidalSubrepresentation F n ω).toSubmodule.map
        (AutomorphicForms.finiteOrderDeterminantMultiplier n χ hχ).toLinearMap =
      (centralCharacterCuspidalSubrepresentation F n (χ ^ n * ω)).toSubmodule := by
  ext f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨centralCharacter_determinantMultiplier n χ ω hg.1,
      IsCuspidal.determinantMultiplier n χ hg.2⟩
  · intro hf
    have hg := centralCharacter_determinantMultiplier n χ⁻¹ (χ ^ n * ω) hf.1
    have hi : (χ⁻¹) ^ n * (χ ^ n * ω) = ω := by
      rw [inv_pow]
      exact inv_mul_cancel_left (χ ^ n) ω
    rw [hi] at hg
    refine ⟨AutomorphicForms.finiteOrderDeterminantMultiplier n χ⁻¹ hχ.inv f,
      ⟨hg, IsCuspidal.determinantMultiplier n χ⁻¹ hf.2⟩, ?_⟩
    apply automorphicToContinuous_injective F n
    change determinantMul n χ (determinantMul n χ⁻¹ (automorphicToContinuous F n f)) =
      automorphicToContinuous F n f
    simpa only [inv_inv (G := HeckeCharacter F)] using
      determinantMul_inv_apply n χ⁻¹ (automorphicToContinuous F n f)

namespace CentralCharacterCuspidalForms

/-- Actual multiplication between the existing specified-character cusp form spaces. -/
def finiteOrderDeterminantMultiplier (χ ω : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    CentralCharacterCuspidalForms F n ω ≃L[ℂ]
      CentralCharacterCuspidalForms F n (χ ^ n * ω) :=
  (AutomorphicForms.finiteOrderDeterminantMultiplier n χ hχ).ofSubmodules _ _
    (centralCharacterCuspidal_map_determinantMultiplier n χ ω hχ)

@[simp]
theorem evaluate_finiteOrderDeterminantMultiplier
    (χ ω : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (f : CentralCharacterCuspidalForms F n ω) (g : AdelicGL F n) :
    evaluate F n
        (automorphicToContinuous F n (finiteOrderDeterminantMultiplier n χ ω hχ f).val) g =
      (χ.adelicDeterminant n g : ℂ) *
        evaluate F n (automorphicToContinuous F n f.val) g := rfl

@[simp]
theorem evaluate_finiteOrderDeterminantMultiplier_symm
    (χ ω : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (f : CentralCharacterCuspidalForms F n (χ ^ n * ω)) (g : AdelicGL F n) :
    evaluate F n
        (automorphicToContinuous F n ((finiteOrderDeterminantMultiplier n χ ω hχ).symm f).val) g =
      ((χ.adelicDeterminant n g)⁻¹ : ℂˣ) *
        evaluate F n (automorphicToContinuous F n f.val) g := rfl

theorem finiteRightAction_determinantMultiplier
    (χ ω : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (d : FiniteAdelicGL F n)
    (f : CentralCharacterCuspidalForms F n ω) :
    centralCharacterCuspidalFiniteRightAction F n (χ ^ n * ω) d
        (finiteOrderDeterminantMultiplier n χ ω hχ f) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) •
        finiteOrderDeterminantMultiplier n χ ω hχ
          (centralCharacterCuspidalFiniteRightAction F n ω d f) := by
  apply Subtype.ext
  exact AutomorphicForms.finiteRightAction_determinantMultiplier n χ hχ d f.val

end CentralCharacterCuspidalForms

namespace CuspidalOperatorRealization

theorem determinantTwist_hasCentralCharacter {r : ℕ}
    (S : CuspidalOperatorRealization F r) (χ ω : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) (hS : S.HasCentralCharacter ω) :
    (S.determinantTwist χ hχ).HasCentralCharacter (χ ^ (r + 1) * ω) :=
  S.realization.determinantTwist_hasCentralCharacter χ ω hχ hS

theorem determinantTwist_hasCentralCharacter_iff {r : ℕ}
    (S : CuspidalOperatorRealization F r) (χ ω : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) :
    (S.determinantTwist χ hχ).HasCentralCharacter (χ ^ (r + 1) * ω) ↔
      S.HasCentralCharacter ω :=
  S.realization.determinantTwist_hasCentralCharacter_iff χ ω hχ

end CuspidalOperatorRealization
end Cuspidal
end Langlands.Automorphic
