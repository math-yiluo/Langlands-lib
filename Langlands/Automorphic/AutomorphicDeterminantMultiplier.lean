import Langlands.Automorphic.DifferentialDeterminantMultiplier
import Langlands.Automorphic.FiniteGrowthDeterminantMultiplier
import Langlands.Automorphic.CuspidalForms
import Langlands.Automorphic.CuspidalDeterminantMultiplier

/-! # Actual finite-order determinant multiplication on automorphic forms -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

local instance automorphicMultiplierRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance automorphicMultiplierContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance automorphicMultiplierFiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance automorphicMultiplierFormGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

/-- All actual automorphic conditions are preserved by finite-order multiplication. -/
theorem mem_automorphic_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    {f : FiniteSmoothRationalFunctions F n} (hf : f ∈ automorphicSubrepresentation F n) :
    FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ f ∈
      automorphicSubrepresentation F n := by
  change IsCenterFinite F n (finiteSmoothInclusion F n f) ∧
    IsInfiniteFinite F n (standardInfiniteCompact F n) f.val ∧
      f.val ∈ polynomialGrowthSubrepresentation F n at hf
  change IsCenterFinite F n (finiteSmoothInclusion F n
      (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ f)) ∧
    IsInfiniteFinite F n (standardInfiniteCompact F n)
      (determinantMultiplier n χ f.val) ∧
    determinantMultiplier n χ f.val ∈ polynomialGrowthSubrepresentation F n
  exact ⟨isCenterFinite_determinantMultiplier n χ hχ hf.1,
    isInfiniteFinite_determinantMultiplier n (standardInfiniteCompact F n) χ hf.2.1,
    (mem_polynomialGrowthSubrepresentation F n _).mpr
      ((hasPolynomialGrowth_determinantMultiplier_iff n χ hχ f.val).mpr
        ((mem_polynomialGrowthSubrepresentation F n _).mp hf.2.2))⟩

private theorem automorphic_map_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (automorphicSubrepresentation F n).toSubmodule.map
        (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ).toLinearMap =
      (automorphicSubrepresentation F n).toSubmodule := by
  ext f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact mem_automorphic_determinantMultiplier n χ hχ hg
  · intro hf
    let g := FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ⁻¹ hχ.inv f
    refine ⟨g, mem_automorphic_determinantMultiplier n χ⁻¹ hχ.inv hf, ?_⟩
    apply Subtype.ext
    change determinantMul n χ (determinantMul n χ⁻¹ f.val) = f.val
    simpa only [inv_inv (G := HeckeCharacter F)] using determinantMul_inv_apply n χ⁻¹ f.val

namespace AutomorphicForms

/-- Actual determinant multiplication as a continuous complex-linear automorphism. -/
def finiteOrderDeterminantMultiplier (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    AutomorphicForms F n ≃L[ℂ] AutomorphicForms F n :=
  (FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ).ofSubmodules _ _
    (automorphic_map_determinantMultiplier n χ hχ)

@[simp]
theorem finiteOrderDeterminantMultiplier_val
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (f : AutomorphicForms F n) :
    (finiteOrderDeterminantMultiplier n χ hχ f).val =
      FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ f.val := rfl

@[simp]
theorem toContinuous_finiteOrderDeterminantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (f : AutomorphicForms F n) :
    automorphicToContinuous F n (finiteOrderDeterminantMultiplier n χ hχ f) =
      determinantMultiplier n χ (automorphicToContinuous F n f) := rfl

@[simp]
theorem evaluate_finiteOrderDeterminantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (f : AutomorphicForms F n)
    (g : AdelicGL F n) :
    evaluate F n (automorphicToContinuous F n (finiteOrderDeterminantMultiplier n χ hχ f)) g =
      (χ.adelicDeterminant n g : ℂ) * evaluate F n (automorphicToContinuous F n f) g := rfl

@[simp]
theorem evaluate_finiteOrderDeterminantMultiplier_symm
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (f : AutomorphicForms F n)
    (g : AdelicGL F n) :
    evaluate F n
        (automorphicToContinuous F n ((finiteOrderDeterminantMultiplier n χ hχ).symm f)) g =
      ((χ.adelicDeterminant n g)⁻¹ : ℂˣ) *
        evaluate F n (automorphicToContinuous F n f) g := rfl

theorem finiteRightAction_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (d : FiniteAdelicGL F n)
    (f : AutomorphicForms F n) :
    automorphicFiniteRightAction F n d (finiteOrderDeterminantMultiplier n χ hχ f) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) •
        finiteOrderDeterminantMultiplier n χ hχ (automorphicFiniteRightAction F n d f) := by
  apply Subtype.ext
  exact FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier_rightAction n χ hχ _ f.val

/-- The actual ambient differentiated functions still satisfy multiplier commutation. -/
theorem envelopingAction_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : AutomorphicForms F n) :
    finiteSmoothEnvelopingAction F n a (finiteOrderDeterminantMultiplier n χ hχ f).val =
      FiniteSmoothRationalFunctions.finiteOrderDeterminantMultiplier n χ hχ
        (finiteSmoothEnvelopingAction F n a f.val) :=
  finiteSmoothEnvelopingAction_determinantMultiplier n χ hχ a f.val

end AutomorphicForms

section Cuspidal

variable [CompactSpace (AdeleQuotient F)]

local instance automorphicMultiplierCuspGroup :
    AddCommGroup (CuspidalAutomorphicForms F n) := Submodule.addCommGroup _

private theorem cuspidalAutomorphic_map_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (cuspidalAutomorphicSubrepresentation F n).toSubmodule.map
        (AutomorphicForms.finiteOrderDeterminantMultiplier n χ hχ).toLinearMap =
      (cuspidalAutomorphicSubrepresentation F n).toSubmodule := by
  ext f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact IsCuspidal.determinantMultiplier n χ hg
  · intro hf
    let g := AutomorphicForms.finiteOrderDeterminantMultiplier n χ⁻¹ hχ.inv f
    refine ⟨g, IsCuspidal.determinantMultiplier n χ⁻¹ hf, ?_⟩
    apply automorphicToContinuous_injective F n
    change determinantMul n χ (determinantMul n χ⁻¹ (automorphicToContinuous F n f)) =
      automorphicToContinuous F n f
    simpa only [inv_inv (G := HeckeCharacter F)] using
      determinantMul_inv_apply n χ⁻¹ (automorphicToContinuous F n f)

namespace CuspidalAutomorphicForms

/-- Actual determinant multiplication on the existing cuspidal automorphic carrier. -/
def finiteOrderDeterminantMultiplier (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    CuspidalAutomorphicForms F n ≃L[ℂ] CuspidalAutomorphicForms F n :=
  (AutomorphicForms.finiteOrderDeterminantMultiplier n χ hχ).ofSubmodules _ _
    (cuspidalAutomorphic_map_determinantMultiplier n χ hχ)

@[simp]
theorem finiteOrderDeterminantMultiplier_val
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (f : CuspidalAutomorphicForms F n) :
    (finiteOrderDeterminantMultiplier n χ hχ f).val =
      AutomorphicForms.finiteOrderDeterminantMultiplier n χ hχ f.val := rfl

@[simp]
theorem evaluate_finiteOrderDeterminantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (f : CuspidalAutomorphicForms F n)
    (g : AdelicGL F n) :
    evaluate F n
        (automorphicToContinuous F n (finiteOrderDeterminantMultiplier n χ hχ f).val) g =
      (χ.adelicDeterminant n g : ℂ) *
        evaluate F n (automorphicToContinuous F n f.val) g := rfl

theorem finiteRightAction_determinantMultiplier
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (d : FiniteAdelicGL F n)
    (f : CuspidalAutomorphicForms F n) :
    cuspidalAutomorphicFiniteRightAction F n d (finiteOrderDeterminantMultiplier n χ hχ f) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) •
        finiteOrderDeterminantMultiplier n χ hχ
          (cuspidalAutomorphicFiniteRightAction F n d f) := by
  apply Subtype.ext
  exact AutomorphicForms.finiteRightAction_determinantMultiplier n χ hχ d f.val

end CuspidalAutomorphicForms
end Cuspidal
end Langlands.Automorphic
