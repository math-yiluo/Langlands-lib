import Langlands.Correspondence.SupercuspidalUniquenessReduction
import Langlands.LocalFactor.NonabelianUniquenessProof

/-!
# Supercuspidal uniqueness from local converse

The published reciprocity and local-constant uniqueness theorems discharge
the two system-comparison premises. Local converse remains an explicit input.
-/

noncomputable section

namespace Langlands.Correspondence

open LocalFactor LocalFactor.CommonClosure

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Arithmetic pair epsilon certificates agree for any two supplied actual
systems, even when their reciprocity families are supplied separately. -/
theorem arithmeticPairEpsilonComparison_of_systems
    {eC₁ eC₂ : ReciprocityFamily F}
    {ε₁ ε₂ : NonabelianSystem.Assignment.{uF, uP} F}
    (h₁ : NonabelianSystem.IsSystem F eC₁ ε₁)
    (h₂ : NonabelianSystem.IsSystem F eC₂ ε₂) :
    ArithmeticPairEpsilonComparison F eC₁ ε₁ h₁ eC₂ ε₂ h₂ :=
  arithmeticPairEpsilonComparison_of_uniqueness F
    (LocalClassField.commonClosureReciprocityUniqueness
      p F F.canonicalTopologicalData)
    (NonabelianSystem.unique F) h₁ h₂

/-- The proved same-family local-constant uniqueness theorem leaves only the
local-converse premise in the existing correspondence uniqueness reduction. -/
theorem supercuspidalCorrespondenceUniqueness_of_localConverse
    (hconverse : RankinSelberg.SupercuspidalLocalConverseStatement.{uF, uA, uA}) :
    SupercuspidalCorrespondenceUniqueness.{uF, uP, uA} F :=
  supercuspidalCorrespondenceUniqueness_of_nonabelianUniqueness F hconverse
    (NonabelianSystem.unique F)

/-- Conditional uniqueness over every p-adic field. Field, parameter and
automorphic carrier universes remain independent. -/
def SupercuspidalCorrespondenceUniquenessFromConverseStatement : Prop :=
  RankinSelberg.SupercuspidalLocalConverseStatement.{uF, uA, uA} →
    ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
      SupercuspidalCorrespondenceUniqueness.{uF, uP, uA} F

theorem supercuspidalCorrespondenceUniquenessFromConverse :
    SupercuspidalCorrespondenceUniquenessFromConverseStatement.{uF, uP, uA} := by
  intro hconverse p _ F
  exact supercuspidalCorrespondenceUniqueness_of_localConverse F hconverse

/-- A supplied existence proof gives the original fieldwise unique-existence
proposition once local converse is supplied. -/
theorem supercuspidalCorrespondenceExistsUnique_of_localConverse_of_existence
    (hconverse : RankinSelberg.SupercuspidalLocalConverseStatement.{uF, uA, uA})
    (hexists : SupercuspidalCorrespondenceExistence.{uF, uP, uA} F) :
    SupercuspidalCorrespondenceExistsUnique.{uF, uP, uA} F := by
  obtain ⟨c, hc⟩ := hexists
  refine ⟨c, hc, ?_⟩
  intro d hd
  exact supercuspidalCorrespondenceUniqueness_of_localConverse F hconverse d c hd hc

/-- Conditional assembly of the unchanged closed target. Neither local
converse nor all-field correspondence existence is asserted by this theorem. -/
theorem supercuspidalCorrespondenceStatement_of_localConverse_of_existence
    (hconverse : RankinSelberg.SupercuspidalLocalConverseStatement.{uF, uA, uA})
    (hexists : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
      SupercuspidalCorrespondenceExistence.{uF, uP, uA} F) :
    SupercuspidalCorrespondenceStatement.{uF, uP, uA} := by
  intro p _ F
  exact supercuspidalCorrespondenceExistsUnique_of_localConverse_of_existence F
    hconverse (hexists p F)

end Langlands.Correspondence
