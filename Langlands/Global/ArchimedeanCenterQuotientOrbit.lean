import Langlands.Global.ArchimedeanCenterFinite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Center orbits as images of an annihilating center quotient -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The actual center-orbit map descends through any center ideal
annihilating the specified smooth function. -/
def centerQuotientOrbitMap (I : Ideal (EnvelopingCenter K n))
    (f : SmoothFunctions K n)
    (hf : ∀ z ∈ I, centerAction K n z f = 0) :
    (EnvelopingCenter K n ⧸ I.restrictScalars ℂ) →ₗ[ℂ] SmoothFunctions K n :=
  (I.restrictScalars ℂ).liftQ (centerOrbitMap K n f) (by
    intro z hz
    exact hf z hz)

@[simp]
theorem centerQuotientOrbitMap_mk (I : Ideal (EnvelopingCenter K n))
    (f : SmoothFunctions K n)
    (hf : ∀ z ∈ I, centerAction K n z f = 0) (z : EnvelopingCenter K n) :
    centerQuotientOrbitMap K n I f hf (Submodule.Quotient.mk z) =
      centerAction K n z f := rfl

theorem centerQuotientOrbitMap_range (I : Ideal (EnvelopingCenter K n))
    (f : SmoothFunctions K n)
    (hf : ∀ z ∈ I, centerAction K n z f = 0) :
    (centerQuotientOrbitMap K n I f hf).range = centerOrbitSpan K n f := by
  exact (Submodule.range_liftQ (I.restrictScalars ℂ) (centerOrbitMap K n f)
    (by intro z hz; exact hf z hz)).trans (centerOrbitSpan_eq_range K n f).symm

/-- A vector annihilated by a finite-codimensional center ideal is
center-finite, because its center orbit is a quotient image. -/
theorem isCenterFinite_of_finite_quotient_annihilates
    (I : Ideal (EnvelopingCenter K n))
    (hI : Module.Finite ℂ (EnvelopingCenter K n ⧸ I.restrictScalars ℂ))
    (f : SmoothFunctions K n)
    (hf : ∀ z ∈ I, centerAction K n z f = 0) :
    IsCenterFinite K n f := by
  have := hI
  change Module.Finite ℂ (centerOrbitSpan K n f)
  rw [← centerQuotientOrbitMap_range K n I f hf]
  exact Module.Finite.range (centerQuotientOrbitMap K n I f hf)

end Langlands.Global.ArchimedeanGL
