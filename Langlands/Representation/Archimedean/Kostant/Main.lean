import Langlands.Representation.Archimedean.Kostant.Assembly
import Langlands.Representation.Archimedean.Kostant.RealTransfer
import Langlands.Representation.Archimedean.GLProductWhittaker

/-!
# Kostant's theorem for finite products of `𝔤𝔩_n(ℂ)` and for `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` (conditional form)
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.Kostant

attribute [local instance 100] LieRing.ofAssociativeRing

universe uV

/-- Kostant's theorem for finite products of `𝔤𝔩_{n i}(ℂ)`, from the nilpotent cone and orbit
statements: the Library proposition `GLProductWhittakerMaximallyFaithfulStatement`. -/
theorem glProductWhittaker_of
    (hNC : ∀ (ι : Type) [Fintype ι] (n : ι → ℕ), NilpotentConeIdealStatement n)
    (hOrb : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ), OrbitVanishingStatement n) :
    GLProductWhittakerMaximallyFaithfulStatement.{uV} := by
  intro ι _ n V _ _ π hχ ℓ hℓ0 a ha hW
  classical
  exact maximallyFaithful_of n (hNC ι n) (hOrb ι n) hχ hℓ0 ha hW

theorem realWhittaker_of
    (hNC : ∀ n : ℕ, NilpotentConeIdealStatement (fun _ : Unit => n))
    (hOrb : ∀ n : ℕ, OrbitVanishingStatement (fun _ : Unit => n)) :
    RealWhittakerMaximallyFaithfulStatement.{uV} := by
  intro n V _ _ π hχ hgen
  obtain ⟨ℓ, hℓ0, a, ha, hW⟩ := hgen
  apply isMaximallyFaithful_of_comp (toGL n)
  refine maximallyFaithful_of (fun _ : Unit => n) (hNC n) (hOrb n)
    (hasInfinitesimalCharacter_comp (toGL n) hχ) hℓ0 (a := fun _ p => Complex.I * a p) ?_
    (isWhittaker_comp π ℓ a hW)
  intro _ p hp
  exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (ha p hp))

end Langlands.Archimedean.Kostant
