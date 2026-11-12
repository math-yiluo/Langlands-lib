import Langlands.Automorphic.StableAutomorphicDeterminantMultiplier
import Langlands.Automorphic.HeckeTwist.AutomorphicMultiplier
import Langlands.Automorphic.HeckeTwist.OperatorConjugation

/-! # Multiplication by any Hecke character on the stable automorphic operator core

Multiplication by `χ ∘ det`, for an arbitrary Hecke character `χ`, preserves the stable
automorphic operator core, and its interaction with the operator actions is recorded.
-/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

local instance heckeStableMultiplierRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance heckeStableMultiplierContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeStableMultiplierFiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeStableMultiplierFormGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance heckeStableMultiplierStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

/-- Whole-algebra conjugation and form preservation imply actual core preservation. -/
theorem mem_automorphicOperatorCore_heckeDeterminantMultiplier
    (χ : HeckeCharacter F)
    {f : FiniteSmoothRationalFunctions F n} (hf : f ∈ automorphicOperatorCore F n) :
    FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ f ∈
      automorphicOperatorCore F n := by
  intro a
  rw [operatorAction_heckeDeterminantMultiplier]
  exact mem_automorphic_heckeDeterminantMultiplier n χ
    (hf (heckeDeterminantOperatorConjugation n χ a))

private theorem automorphicOperatorCore_map_determinantMultiplier
    (χ : HeckeCharacter F) :
    (automorphicOperatorCore F n).toSubmodule.map
        (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ).toLinearMap =
      (automorphicOperatorCore F n).toSubmodule := by
  ext f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact mem_automorphicOperatorCore_heckeDeterminantMultiplier n χ hg
  · intro hf
    let g := FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ⁻¹ f
    refine ⟨g, mem_automorphicOperatorCore_heckeDeterminantMultiplier n χ⁻¹ hf, ?_⟩
    apply Subtype.ext
    change determinantMul n χ (determinantMul n χ⁻¹ f.val) = f.val
    simpa only [inv_inv (G := HeckeCharacter F)] using determinantMul_inv_apply n χ⁻¹ f.val

namespace StableAutomorphicFunctions

/-- Restrict actual multiplication to the constructed stable operator core. -/
def heckeDeterminantMultiplier (χ : HeckeCharacter F) :
    StableAutomorphicFunctions F n ≃L[ℂ] StableAutomorphicFunctions F n :=
  (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ).ofSubmodules _ _
    (automorphicOperatorCore_map_determinantMultiplier n χ)

@[simp]
theorem heckeDeterminantMultiplier_val
    (χ : HeckeCharacter F)
    (f : StableAutomorphicFunctions F n) :
    (heckeDeterminantMultiplier n χ f).val =
      FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ f.val := rfl

theorem operatorAction_heckeDeterminantMultiplier
    (χ : HeckeCharacter F)
    (a : automorphicOperatorAlgebra F n) (f : StableAutomorphicFunctions F n) :
    stableAutomorphicAction F n a (heckeDeterminantMultiplier n χ f) =
      heckeDeterminantMultiplier n χ
        (stableAutomorphicAction F n (heckeDeterminantOperatorConjugation n χ a) f) := by
  apply Subtype.ext
  exact Langlands.Automorphic.operatorAction_heckeDeterminantMultiplier n χ a f.val

theorem finiteAction_heckeDeterminantMultiplier
    (χ : HeckeCharacter F) (d : FiniteAdelicGL F n)
    (f : StableAutomorphicFunctions F n) :
    stableAutomorphicFiniteAction F n d (heckeDeterminantMultiplier n χ f) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) •
        heckeDeterminantMultiplier n χ (stableAutomorphicFiniteAction F n d f) := by
  apply Subtype.ext
  exact FiniteSmoothRationalFunctions.heckeDeterminantMultiplier_rightAction n χ _ f.val

theorem compactAction_heckeDeterminantMultiplier
    (χ : HeckeCharacter F) (k : standardInfiniteCompact F n)
    (f : StableAutomorphicFunctions F n) :
    stableAutomorphicCompactAction F n k (heckeDeterminantMultiplier n χ f) =
      (χ.adelicDeterminant n (AdelicGL.ofInfinite F n k.val) : ℂ) •
        heckeDeterminantMultiplier n χ (stableAutomorphicCompactAction F n k f) := by
  apply Subtype.ext
  exact FiniteSmoothRationalFunctions.heckeDeterminantMultiplier_rightAction n χ _ f.val

theorem envelopingAction_heckeDeterminantMultiplier
    (χ : HeckeCharacter F)
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : StableAutomorphicFunctions F n) :
    stableAutomorphicEnvelopingAction F n a (heckeDeterminantMultiplier n χ f) =
      heckeDeterminantMultiplier n χ
        (stableAutomorphicEnvelopingAction F n (heckeEnvelopingShift n χ a) f) := by
  apply Subtype.ext
  exact finiteSmoothEnvelopingAction_heckeDeterminantMultiplier n χ a f.val

@[simp]
theorem inclusion_heckeDeterminantMultiplier
    (χ : HeckeCharacter F)
    (f : StableAutomorphicFunctions F n) :
    stableAutomorphicInclusion F n (heckeDeterminantMultiplier n χ f) =
      AutomorphicForms.heckeDeterminantMultiplier n χ
        (stableAutomorphicInclusion F n f) := rfl

@[simp]
theorem evaluate_heckeDeterminantMultiplier
    (χ : HeckeCharacter F)
    (f : StableAutomorphicFunctions F n) (g : AdelicGL F n) :
    evaluate F n (heckeDeterminantMultiplier n χ f).val.val g =
      (χ.adelicDeterminant n g : ℂ) * evaluate F n f.val.val g := rfl

@[simp]
theorem evaluate_heckeDeterminantMultiplier_symm
    (χ : HeckeCharacter F)
    (f : StableAutomorphicFunctions F n) (g : AdelicGL F n) :
    evaluate F n ((heckeDeterminantMultiplier n χ).symm f).val.val g =
      ((χ.adelicDeterminant n g)⁻¹ : ℂˣ) * evaluate F n f.val.val g := rfl

end StableAutomorphicFunctions
end Langlands.Automorphic
