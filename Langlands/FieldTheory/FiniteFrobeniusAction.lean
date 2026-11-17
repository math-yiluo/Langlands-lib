import Mathlib.FieldTheory.Finite.Extension
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Field.ULift
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Realizing a finite-order element as the image of finite-field Frobenius -/

noncomputable section

universe u v

namespace Langlands.FieldTheory

variable (k : Type u) [Field k] [Fintype k]
    {A : Type v} [Group A] (θ : A)

/-- A finite Galois extension with a prescribed Frobenius value in a group. -/
structure FiniteFrobeniusAction where
  extension : Type u
  [field : Field extension]
  [algebra : Algebra k extension]
  [finite : Finite extension]
  [finiteDimensional : FiniteDimensional k extension]
  [isGalois : IsGalois k extension]
  action : (extension ≃ₐ[k] extension) →* A
  frobenius : action (FiniteField.frobeniusAlgEquivOfAlgebraic k extension) = θ
  degree : Module.finrank k extension = orderOf θ

attribute [instance] FiniteFrobeniusAction.field FiniteFrobeniusAction.algebra
  FiniteFrobeniusAction.finite FiniteFrobeniusAction.finiteDimensional
  FiniteFrobeniusAction.isGalois

/-- A finite-order element is the image of arithmetic Frobenius for an action
of the Galois group of an extension of degree equal to its order. -/
def finiteFrobeniusAction (hθ : IsOfFinOrder θ) : FiniteFrobeniusAction k θ := by
  apply Classical.choice
  obtain ⟨p, hp⟩ := CharP.exists k
  let : CharP k p := hp
  let : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  let : NeZero (orderOf θ) := ⟨hθ.orderOf_pos.ne'⟩
  let K := ULift.{u} (FiniteField.Extension k p (orderOf θ))
  let : Field K := inferInstance
  let : Algebra k K := inferInstance
  let : Finite K := inferInstance
  let : FiniteDimensional k K := Module.Finite.of_finite
  let : IsGalois k K := inferInstance
  have hdeg : Module.finrank k K = orderOf θ := by
    rw [finrank_ulift, FiniteField.finrank_extension]
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic k K
  have hgen : ∀ σ : K ≃ₐ[k] K, σ ∈ Subgroup.zpowers φ := by
    intro σ
    obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k K).surjective σ
    exact Subgroup.mem_zpowers_iff.mpr ⟨(n.val : ℤ), by simpa only [zpow_natCast] using hn⟩
  have hdiv : orderOf θ ∣ orderOf φ := by
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, hdeg]
  exact
    ⟨{
      extension := K
      action := monoidHomOfForallMemZpowers hgen hdiv
      frobenius := monoidHomOfForallMemZpowers_apply_gen hgen hdiv
      degree := hdeg }⟩

end Langlands.FieldTheory
