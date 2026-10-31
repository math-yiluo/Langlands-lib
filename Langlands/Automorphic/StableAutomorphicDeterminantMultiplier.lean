import Langlands.Automorphic.AutomorphicDeterminantMultiplier
import Langlands.Automorphic.DeterminantOperatorConjugation

/-! # Actual determinant multiplication on the stable automorphic operator core -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

local instance stableMultiplierRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance stableMultiplierContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance stableMultiplierFiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance stableMultiplierFormGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance stableMultiplierStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

/-- Whole-algebra conjugation and form preservation imply actual core preservation. -/
theorem mem_automorphicOperatorCore_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    {f : FiniteSmoothRationalFunctions F n} (hf : f ∈ automorphicOperatorCore F n) :
    FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ f ∈
      automorphicOperatorCore F n := by
  intro a
  rw [operatorAction_determinantMultiplier]
  exact mem_automorphic_determinantMultiplier n χ hχ
    (hf (determinantOperatorConjugation n χ hχ a))

private theorem automorphicOperatorCore_map_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (automorphicOperatorCore F n).toSubmodule.map
        (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ).toLinearMap =
      (automorphicOperatorCore F n).toSubmodule := by
  ext f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact mem_automorphicOperatorCore_determinantMultiplier n χ hχ hg
  · intro hf
    let g := FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ⁻¹ hχ.inv f
    refine ⟨g, mem_automorphicOperatorCore_determinantMultiplier n χ⁻¹ hχ.inv hf, ?_⟩
    apply Subtype.ext
    change determinantMul n χ (determinantMul n χ⁻¹ f.val) = f.val
    simpa only [inv_inv (G := HeckeCharacter F)] using determinantMul_inv_apply n χ⁻¹ f.val

namespace StableAutomorphicFunctions

/-- Restrict actual multiplication to the constructed stable operator core. -/
def finiteOrderDeterminantMultiplier (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    StableAutomorphicFunctions F n ≃L[ℂ] StableAutomorphicFunctions F n :=
  (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ).ofSubmodules _ _
    (automorphicOperatorCore_map_determinantMultiplier n χ hχ)

@[simp]
theorem finiteOrderDeterminantMultiplier_val
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (f : StableAutomorphicFunctions F n) :
    (finiteOrderDeterminantMultiplier n χ hχ f).val =
      FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ f.val := rfl

theorem operatorAction_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (a : automorphicOperatorAlgebra F n) (f : StableAutomorphicFunctions F n) :
    stableAutomorphicAction F n a (finiteOrderDeterminantMultiplier n χ hχ f) =
      finiteOrderDeterminantMultiplier n χ hχ
        (stableAutomorphicAction F n (determinantOperatorConjugation n χ hχ a) f) := by
  apply Subtype.ext
  exact Langlands.Automorphic.operatorAction_determinantMultiplier n χ hχ a f.val

theorem finiteAction_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (d : FiniteAdelicGL F n)
    (f : StableAutomorphicFunctions F n) :
    stableAutomorphicFiniteAction F n d (finiteOrderDeterminantMultiplier n χ hχ f) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) •
        finiteOrderDeterminantMultiplier n χ hχ (stableAutomorphicFiniteAction F n d f) := by
  apply Subtype.ext
  exact FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier_rightAction n χ hχ _ f.val

theorem compactAction_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (k : standardInfiniteCompact F n)
    (f : StableAutomorphicFunctions F n) :
    stableAutomorphicCompactAction F n k (finiteOrderDeterminantMultiplier n χ hχ f) =
      (χ.adelicDeterminant n (AdelicGL.ofInfinite F n k.val) : ℂ) •
        finiteOrderDeterminantMultiplier n χ hχ (stableAutomorphicCompactAction F n k f) := by
  apply Subtype.ext
  exact FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier_rightAction n χ hχ _ f.val

theorem envelopingAction_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : StableAutomorphicFunctions F n) :
    stableAutomorphicEnvelopingAction F n a (finiteOrderDeterminantMultiplier n χ hχ f) =
      finiteOrderDeterminantMultiplier n χ hχ (stableAutomorphicEnvelopingAction F n a f) := by
  apply Subtype.ext
  exact finiteSmoothEnvelopingAction_determinantMultiplier n χ hχ a f.val

@[simp]
theorem inclusion_finiteOrderDeterminantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (f : StableAutomorphicFunctions F n) :
    stableAutomorphicInclusion F n (finiteOrderDeterminantMultiplier n χ hχ f) =
      AutomorphicForms.finiteOrderDeterminantMultiplier n χ hχ
        (stableAutomorphicInclusion F n f) := rfl

@[simp]
theorem evaluate_finiteOrderDeterminantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (f : StableAutomorphicFunctions F n) (g : AdelicGL F n) :
    evaluate F n (finiteOrderDeterminantMultiplier n χ hχ f).val.val g =
      (χ.adelicDeterminant n g : ℂ) * evaluate F n f.val.val g := rfl

@[simp]
theorem evaluate_finiteOrderDeterminantMultiplier_symm
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (f : StableAutomorphicFunctions F n) (g : AdelicGL F n) :
    evaluate F n ((finiteOrderDeterminantMultiplier n χ hχ).symm f).val.val g =
      ((χ.adelicDeterminant n g)⁻¹ : ℂˣ) * evaluate F n f.val.val g := rfl

end StableAutomorphicFunctions
end Langlands.Automorphic
