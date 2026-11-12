import Langlands.Automorphic.HeckeTwist.DifferentialMultiplier
import Langlands.Automorphic.AutomorphicDeterminantMultiplier
import Langlands.Global.ArchimedeanCharacterGrowth

/-! # Determinant multiplication by any Hecke character on automorphic forms

Multiplication by `χ ∘ det` keeps polynomial growth, because the archimedean determinant
factor of `χ` has polynomial growth. With the smooth, `K_∞`-finite and center-finite cases
of the earlier modules, it preserves the automorphic forms, for every Hecke character.
-/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

local instance heckeAutomorphicMultiplierRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance heckeAutomorphicMultiplierContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeAutomorphicMultiplierFiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeAutomorphicMultiplierFormGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

/-- Multiplication by `χ ∘ det` keeps polynomial growth on every infinite slice. -/
theorem hasPolynomialGrowth_heckeDeterminantMultiplier (χ : HeckeCharacter F)
    {f : ContinuousRationalFunctions F n} (hf : HasPolynomialGrowth F n f) :
    HasPolynomialGrowth F n (determinantMultiplier n χ f) := by
  intro b
  have h := ((χ.hasPolynomialGrowth_adelicDeterminant_ofInfinite n).mul (hf b)).smul
    (χ.adelicDeterminant n (AdelicGL.ofFinite F n b) : ℂ)
  convert h using 1
  funext a
  change (χ.adelicDeterminant n (AdelicGL.pair F n a b) : ℂ) *
      evaluate F n f (AdelicGL.pair F n a b) =
    (χ.adelicDeterminant n (AdelicGL.ofFinite F n b) : ℂ) *
      ((χ.infiniteDeterminantCharacter n a : ℂ) * evaluate F n f (AdelicGL.pair F n a b))
  rw [HeckeCharacter.adelicDeterminant_pair_val, mul_assoc]

/-- All automorphic conditions are preserved by multiplication by any Hecke character. -/
theorem mem_automorphic_heckeDeterminantMultiplier (χ : HeckeCharacter F)
    {f : FiniteSmoothRationalFunctions F n} (hf : f ∈ automorphicSubrepresentation F n) :
    FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ f ∈
      automorphicSubrepresentation F n := by
  change IsCenterFinite F n (finiteSmoothInclusion F n f) ∧
    IsInfiniteFinite F n (standardInfiniteCompact F n) f.val ∧
      f.val ∈ polynomialGrowthSubrepresentation F n at hf
  change IsCenterFinite F n (finiteSmoothInclusion F n
      (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ f)) ∧
    IsInfiniteFinite F n (standardInfiniteCompact F n)
      (determinantMultiplier n χ f.val) ∧
    determinantMultiplier n χ f.val ∈ polynomialGrowthSubrepresentation F n
  exact ⟨isCenterFinite_heckeDeterminantMultiplier n χ hf.1,
    isInfiniteFinite_determinantMultiplier n (standardInfiniteCompact F n) χ hf.2.1,
    (mem_polynomialGrowthSubrepresentation F n _).mpr
      (hasPolynomialGrowth_heckeDeterminantMultiplier n χ
        ((mem_polynomialGrowthSubrepresentation F n _).mp hf.2.2))⟩

private theorem automorphic_map_heckeDeterminantMultiplier (χ : HeckeCharacter F) :
    (automorphicSubrepresentation F n).toSubmodule.map
        (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ).toLinearMap =
      (automorphicSubrepresentation F n).toSubmodule := by
  ext f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact mem_automorphic_heckeDeterminantMultiplier n χ hg
  · intro hf
    let g := FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ⁻¹ f
    refine ⟨g, mem_automorphic_heckeDeterminantMultiplier n χ⁻¹ hf, ?_⟩
    apply Subtype.ext
    change determinantMul n χ (determinantMul n χ⁻¹ f.val) = f.val
    simpa only [inv_inv (G := HeckeCharacter F)] using determinantMul_inv_apply n χ⁻¹ f.val

namespace AutomorphicForms

/-- Multiplication by `χ ∘ det` on automorphic forms, for any Hecke character. -/
def heckeDeterminantMultiplier (χ : HeckeCharacter F) :
    AutomorphicForms F n ≃L[ℂ] AutomorphicForms F n :=
  (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ).ofSubmodules _ _
    (automorphic_map_heckeDeterminantMultiplier n χ)

@[simp]
theorem heckeDeterminantMultiplier_val (χ : HeckeCharacter F) (f : AutomorphicForms F n) :
    (heckeDeterminantMultiplier n χ f).val =
      FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ f.val := rfl

@[simp]
theorem toContinuous_heckeDeterminantMultiplier (χ : HeckeCharacter F)
    (f : AutomorphicForms F n) :
    automorphicToContinuous F n (heckeDeterminantMultiplier n χ f) =
      determinantMultiplier n χ (automorphicToContinuous F n f) := rfl

@[simp]
theorem evaluate_heckeDeterminantMultiplier (χ : HeckeCharacter F) (f : AutomorphicForms F n)
    (g : AdelicGL F n) :
    evaluate F n (automorphicToContinuous F n (heckeDeterminantMultiplier n χ f)) g =
      (χ.adelicDeterminant n g : ℂ) * evaluate F n (automorphicToContinuous F n f) g := rfl

@[simp]
theorem evaluate_heckeDeterminantMultiplier_symm (χ : HeckeCharacter F)
    (f : AutomorphicForms F n) (g : AdelicGL F n) :
    evaluate F n
        (automorphicToContinuous F n ((heckeDeterminantMultiplier n χ).symm f)) g =
      ((χ.adelicDeterminant n g)⁻¹ : ℂˣ) *
        evaluate F n (automorphicToContinuous F n f) g := rfl

theorem finiteRightAction_heckeDeterminantMultiplier (χ : HeckeCharacter F)
    (d : FiniteAdelicGL F n) (f : AutomorphicForms F n) :
    automorphicFiniteRightAction F n d (heckeDeterminantMultiplier n χ f) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) •
        heckeDeterminantMultiplier n χ (automorphicFiniteRightAction F n d f) := by
  apply Subtype.ext
  exact FiniteSmoothRationalFunctions.heckeDeterminantMultiplier_rightAction n χ _ f.val

/-- A differential operator applied to a multiplied form is the multiplier applied to the
shifted operator. -/
theorem envelopingAction_heckeDeterminantMultiplier (χ : HeckeCharacter F)
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : AutomorphicForms F n) :
    finiteSmoothEnvelopingAction F n a (heckeDeterminantMultiplier n χ f).val =
      FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ
        (finiteSmoothEnvelopingAction F n (heckeEnvelopingShift n χ a) f.val) :=
  finiteSmoothEnvelopingAction_heckeDeterminantMultiplier n χ a f.val

end AutomorphicForms
end Langlands.Automorphic
