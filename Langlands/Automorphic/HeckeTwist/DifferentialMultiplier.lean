import Langlands.Automorphic.HeckeTwist.SmoothMultiplier
import Langlands.Automorphic.DifferentialCenterFinite
import Langlands.Global.ArchimedeanCharacterMultiplier

/-! # Determinant multiplication by any Hecke character and adelic differential operators

On every infinite slice, multiplication by `χ ∘ det` is a constant times multiplication by
the smooth archimedean character `a ↦ χ(det a)`. Hence the enveloping action commutes with
the multiplier after the shift automorphism of the enveloping algebra attached to that
character, and center finiteness is preserved.
-/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

local instance heckeDifferentialRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance heckeDifferentialContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeDifferentialFiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _

/-- The shift automorphism of the enveloping algebra attached to `a ↦ χ(det a)`. -/
def heckeEnvelopingShift (χ : HeckeCharacter F) :
    ArchimedeanGL.EnvelopingAlgebra F n →ₐ[ℂ] ArchimedeanGL.EnvelopingAlgebra F n :=
  ArchimedeanGL.characterShift (χ.infiniteDeterminantCharacter n)
    (χ.infiniteDeterminantCharacter_mem_smoothFunctions n)

/-- The shift restricted to the center of the enveloping algebra. -/
def heckeCenterShift (χ : HeckeCharacter F) (z : ArchimedeanGL.EnvelopingCenter F n) :
    ArchimedeanGL.EnvelopingCenter F n :=
  ArchimedeanGL.characterCenterShift (χ.infiniteDeterminantCharacter n)
    (χ.infiniteDeterminantCharacter_mem_smoothFunctions n) z

@[simp]
theorem centerInclusion_heckeCenterShift (χ : HeckeCharacter F)
    (z : ArchimedeanGL.EnvelopingCenter F n) :
    ArchimedeanGL.centerInclusion F n (heckeCenterShift n χ z) =
      heckeEnvelopingShift n χ (ArchimedeanGL.centerInclusion F n z) := rfl

/-- On an infinite slice the multiplier is the finite value times the archimedean character
multiplier. -/
theorem finiteSmoothSlice_heckeDeterminantMultiplier (χ : HeckeCharacter F)
    (b : FiniteAdelicGL F n) (f : FiniteSmoothRationalFunctions F n) :
    finiteSmoothSlice F n b (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ f) =
      (χ.adelicDeterminant n (AdelicGL.ofFinite F n b) : ℂ) •
        ArchimedeanGL.characterMultiplier (χ.infiniteDeterminantCharacter n)
          (χ.infiniteDeterminantCharacter_mem_smoothFunctions n)
          (finiteSmoothSlice F n b f) := by
  apply Subtype.ext
  funext a
  change (χ.adelicDeterminant n (AdelicGL.pair F n a b) : ℂ) *
      evaluate F n f.val (AdelicGL.pair F n a b) =
    (χ.adelicDeterminant n (AdelicGL.ofFinite F n b) : ℂ) *
      ((χ.infiniteDeterminantCharacter n a : ℂ) * evaluate F n f.val (AdelicGL.pair F n a b))
  rw [HeckeCharacter.adelicDeterminant_pair_val, mul_assoc]

/-- Every enveloping operator composed with the multiplier is the multiplier composed with
the shifted enveloping operator. -/
theorem finiteSmoothEnvelopingAction_heckeDeterminantMultiplier (χ : HeckeCharacter F)
    (u : ArchimedeanGL.EnvelopingAlgebra F n) (f : FiniteSmoothRationalFunctions F n) :
    finiteSmoothEnvelopingAction F n u
        (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ f) =
      FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ
        (finiteSmoothEnvelopingAction F n (heckeEnvelopingShift n χ u) f) := by
  apply finiteSmoothSlice_injective F n
  funext b
  simp only [finiteSmoothSlice_envelopingAction, finiteSmoothSlice_heckeDeterminantMultiplier,
    map_smul, ArchimedeanGL.envelopingAction_characterMultiplier_apply]
  rfl

theorem finiteSmoothCenterAction_heckeDeterminantMultiplier (χ : HeckeCharacter F)
    (z : ArchimedeanGL.EnvelopingCenter F n) (f : FiniteSmoothRationalFunctions F n) :
    finiteSmoothCenterAction F n z
        (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ f) =
      FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ
        (finiteSmoothCenterAction F n (heckeCenterShift n χ z) f) :=
  finiteSmoothEnvelopingAction_heckeDeterminantMultiplier n χ
    (ArchimedeanGL.centerInclusion F n z) f

/-- The center orbit of a multiplied function lies in the image of the center orbit of the
function. -/
theorem orbitSpan_heckeDeterminantMultiplier_le (χ : HeckeCharacter F)
    (f : FiniteSmoothRationalFunctions F n) :
    FiniteVectors.orbitSpan (finiteSmoothCenterRepresentation F n)
        (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ f) ≤
      (FiniteVectors.orbitSpan (finiteSmoothCenterRepresentation F n) f).map
        (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ).toLinearMap := by
  apply Submodule.span_le.mpr
  rintro _ ⟨z, rfl⟩
  refine ⟨finiteSmoothCenterAction F n (heckeCenterShift n χ z) f,
    FiniteVectors.action_mem_orbitSpan _ (heckeCenterShift n χ z) f, ?_⟩
  exact (finiteSmoothCenterAction_heckeDeterminantMultiplier n χ z f).symm

/-- Center finiteness is preserved by every Hecke multiplier. -/
theorem isCenterFinite_heckeDeterminantMultiplier (χ : HeckeCharacter F)
    {f : FiniteSmoothRationalFunctions F n}
    (hf : IsCenterFinite F n (finiteSmoothInclusion F n f)) :
    IsCenterFinite F n (finiteSmoothInclusion F n
      (FiniteSmoothRationalFunctions.heckeDeterminantMultiplier n χ f)) := by
  apply (isCenterFinite_iff_finiteSmoothCenterVector F n _).mpr
  have hv : FiniteVectors.IsFiniteVector (finiteSmoothCenterRepresentation F n) f :=
    (isCenterFinite_iff_finiteSmoothCenterVector F n f).mp hf
  have : Module.Finite ℂ (FiniteVectors.orbitSpan (finiteSmoothCenterRepresentation F n) f) :=
    hv
  exact Submodule.finiteDimensional_of_le (orbitSpan_heckeDeterminantMultiplier_le n χ f)

end Langlands.Automorphic
