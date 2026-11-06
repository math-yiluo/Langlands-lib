import Langlands.Correspondence.ArithmeticFactors

/-!
# Comparing the supplied arithmetic systems in correspondence predicates

The comparison relation retains both actual assignments. Its uniqueness
consequence assumes the two precise uniqueness inputs explicitly.
-/

noncomputable section

namespace Langlands.Correspondence

open LocalFactor LocalFactor.CommonClosure

universe uF uP

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- The arithmetic pair epsilon certificate has the same meaning for two
specified actual common-closure systems. -/
def ArithmeticPairEpsilonComparison
    (eC₁ : ReciprocityFamily F) (ε₁ : NonabelianSystem.Assignment.{uF, uP} F)
    (h₁ : NonabelianSystem.IsSystem F eC₁ ε₁)
    (eC₂ : ReciprocityFamily F) (ε₂ : NonabelianSystem.Assignment.{uF, uP} F)
    (h₂ : NonabelianSystem.IsSystem F eC₂ ε₂) : Prop :=
  ∀ (ψ : NontrivialAdditiveCharacter F) (X Y : LocalPairClass.{uF, uP} F)
    (c : ℂˣ) (m : ℤ),
    IsArithmeticPairEpsilonFactor F eC₁ ε₁ h₁ ψ X Y c m ↔
      IsArithmeticPairEpsilonFactor F eC₂ ε₂ h₂ ψ X Y c m

/-- A fixed common-closure family can be the base extension of at most one
standalone reciprocity candidate. No reciprocity uniqueness theorem is used. -/
theorem IsBaseReciprocity.candidate_unique
    {e₁ e₂ : ReciprocityCandidate F} {eC : ReciprocityFamily F}
    (h₁ : IsBaseReciprocity F e₁ eC) (h₂ : IsBaseReciprocity F e₂ eC) :
    e₁ = e₂ := by
  have hbase : weilSubgroup F (baseExtension F) = ⊤ := by
    change Subgroup.comap _
      (⊥ : IntermediateField F.Carrier (AlgebraicClosure F.Carrier)).fixingSubgroup = ⊤
    rw [IntermediateField.fixingSubgroup_bot]
    exact Subgroup.comap_top _
  apply ContinuousMulEquiv.ext
  intro x
  refine QuotientGroup.induction_on x ?_
  intro w
  let w' : weilSubgroup F (baseExtension F) :=
    ⟨w, by rw [hbase]; trivial⟩
  apply Units.ext
  exact (h₁ w').symm.trans (h₂ w')

/-- Equality of the common-closure families identifies their compatible
standalone candidates, without any new single-field uniqueness premise. -/
theorem IsBaseReciprocity.candidate_eq_of_family_eq
    {e₁ e₂ : ReciprocityCandidate F} {eC₁ eC₂ : ReciprocityFamily F}
    (h₁ : IsBaseReciprocity F e₁ eC₁) (h₂ : IsBaseReciprocity F e₂ eC₂)
    (he : eC₁ = eC₂) : e₁ = e₂ := by
  subst eC₂
  exact h₁.candidate_unique F h₂

/-- The certificate depends only on the family and assignment, not on the
proof of the system laws. -/
theorem arithmeticPairEpsilonComparison_of_eq
    {eC₁ eC₂ : ReciprocityFamily F}
    {ε₁ ε₂ : NonabelianSystem.Assignment.{uF, uP} F}
    (h₁ : NonabelianSystem.IsSystem F eC₁ ε₁)
    (h₂ : NonabelianSystem.IsSystem F eC₂ ε₂)
    (he : eC₁ = eC₂) (hε : ε₁ = ε₂) :
    ArithmeticPairEpsilonComparison F eC₁ ε₁ h₁ eC₂ ε₂ h₂ := by
  subst eC₂
  subst ε₂
  intro ψ X Y c m
  rfl

/-- Local reciprocity-family uniqueness and same-family assignment uniqueness
jointly compare the two supplied systems in all actual arithmetic certificates.
Both uniqueness inputs are explicit premises. -/
theorem arithmeticPairEpsilonComparison_of_uniqueness
    (hRec : ∀ eC₁ eC₂ : ReciprocityFamily F,
      NormalizedReciprocity F eC₁ → NormalizedReciprocity F eC₂ → eC₁ = eC₂)
    (hUnique : ∀ eC : ReciprocityFamily F, NonabelianSystem.Unique.{uF, uP} F eC)
    {eC₁ eC₂ : ReciprocityFamily F}
    {ε₁ ε₂ : NonabelianSystem.Assignment.{uF, uP} F}
    (h₁ : NonabelianSystem.IsSystem F eC₁ ε₁)
    (h₂ : NonabelianSystem.IsSystem F eC₂ ε₂) :
    ArithmeticPairEpsilonComparison F eC₁ ε₁ h₁ eC₂ ε₂ h₂ := by
  have he : eC₁ = eC₂ := hRec eC₁ eC₂ h₁.1 h₂.1
  subst eC₂
  have hε : ε₁ = ε₂ := hUnique eC₁ ε₁ ε₂ h₁ h₂
  exact arithmeticPairEpsilonComparison_of_eq F h₁ h₂ rfl hε

end Langlands.Correspondence
