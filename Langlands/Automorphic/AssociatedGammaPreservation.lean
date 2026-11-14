import Langlands.Automorphic.AssociatedGammaCommonInputs

/-!
# Gamma preservation for the two Hecke families

The archimedean factors of both families do not depend on the character, and the finite
factors at a place depend only on the local component of the character. Hence both
preservation inputs of the two-twist engine hold by rewriting.
-/

noncomputable section

set_option autoImplicit false

universe u uQ uV uE

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.FunctionalEquationComparison
open Langlands.Global.CuspidalPairFunctionalEquation

variable {c : FundamentalClass.ClassFamily.{u}} {F E : Type u} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

/-- Meromorphic equality is reflexive. -/
theorem meromorphicEq_refl (f : ℂ → ℂ) : MeromorphicEq f f := fun _ => Filter.EventuallyEq.rfl

/-- The local component of the trivial Hecke character is trivial. -/
theorem _root_.Langlands.Global.HeckeCharacter.finiteComponent_one (z : FinitePlace F) :
    (1 : HeckeCharacter F).finiteComponent z = 1 := by
  ext x
  rfl

/-- Archimedean gamma preservation for the two families. -/
theorem infinityGammaPreservation_families
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
    [CompactSpace (AdeleQuotient F)] {r t : ℕ}
    {S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (D : AutomorphicTwistSetup.{u, uQ} ψ r t) (A : ArithmeticTwistSetup.{u, uV, uE} ψ S S')
    (arch : NumberField.InfinitePlace F → LocalFactors) :
    InfinityGammaPreservation F (HeckeEulerFamily.ofLocalFactors D.localFactors)
      (HeckeEulerFamily.ofLocalFactors (A.localFactors arch)) := fun χ _ _ w => by
  refine ⟨?_, ?_⟩
  · change MeromorphicEq (D.localFactors χ (.inl w)).gamma (D.localFactors 1 (.inl w)).gamma
    rw [D.localFactors_inl χ w]
    exact meromorphicEq_refl _
  · change MeromorphicEq (A.localFactors arch χ (.inl w)).gamma
      (A.localFactors arch 1 (.inl w)).gamma
    rw [A.localFactors_inl arch χ w]
    exact meromorphicEq_refl _

/-- Finite gamma preservation at `v` for the two families. -/
theorem finiteGammaPreservation_families
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
    [CompactSpace (AdeleQuotient F)] {r t : ℕ}
    {S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (D : AutomorphicTwistSetup.{u, uQ} ψ r t) (A : ArithmeticTwistSetup.{u, uV, uE} ψ S S')
    (arch : NumberField.InfinitePlace F → LocalFactors) (v : FinitePlace F) :
    FiniteGammaPreservation F v (HeckeEulerFamily.ofLocalFactors D.localFactors)
      (HeckeEulerFamily.ofLocalFactors (A.localFactors arch)) := fun χ _ hχ => by
  have h : χ.finiteComponent v = (1 : HeckeCharacter F).finiteComponent v := by
    rw [hχ, HeckeCharacter.finiteComponent_one]
  refine ⟨?_, ?_⟩
  · change MeromorphicEq (D.localFactors χ (.inr v)).gamma (D.localFactors 1 (.inr v)).gamma
    rw [D.localFactors_inr_of_finiteComponent_eq h]
    exact meromorphicEq_refl _
  · change MeromorphicEq (A.localFactors arch χ (.inr v)).gamma
      (A.localFactors arch 1 (.inr v)).gamma
    rw [A.localFactors_inr_of_finiteComponent_eq arch h]
    exact meromorphicEq_refl _

end Langlands.ClassField.Global.RelativeWeilGroup
