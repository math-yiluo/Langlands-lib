import Langlands.Global.RankinSelberg.RealAscendingWhittakerEvaluation
import Langlands.Global.RankinSelberg.RealAscendingWhittakerMultiplicity
import Langlands.Global.RankinSelberg.RealExactStandardEvaluation
import Langlands.Global.RankinSelberg.RealWhittakerUniformGrowth

/-! # Exact Whittaker multiplicity for real character principal series -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries

open RealStandardCompactBanach (exists_boundedForm_of_characterEvaluation)
open RealExactStandardEvaluation (exists_standardEvaluation)

/-- Every exact coefficient map on a real character principal series is proportional to any
nonzero exact coefficient map for the same additive character. -/
def RealExactCharacterWhittakerUniquenessStatement : Prop :=
  ∀ (r : ℕ) (cs : List RealCharacterData), realRank (cs.map RealBlock.character) = r + 1 →
    ∀ a : ℝˣ, HasProportionalWhittakerIntertwiners r (cs.map RealBlock.character) a

theorem realExactCharacterWhittakerUniqueness : RealExactCharacterWhittakerUniquenessStatement := by
  intro r cs hr a B C hB hC hCne
  let ds := cs.map RealBlock.character
  have hds : RealStrictCharacterLanglandsQuotient.IsCharacterList ds := by
    intro d hd
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hd
    exact ⟨c, rfl⟩
  obtain ⟨L₁, hL₁⟩ := exists_standardEvaluation cs a C hC
  obtain ⟨L₂, hL₂⟩ := exists_standardEvaluation cs a B hB
  obtain ⟨ℓ₁, hBound₁, hCov₁, hEval₁⟩ :=
    exists_boundedForm_of_characterEvaluation ds hds a L₁ hL₁.2
  obtain ⟨ℓ₂, hBound₂, hCov₂, hEval₂⟩ :=
    exists_boundedForm_of_characterEvaluation ds hds a L₂ hL₂.2
  have hMatch₁ (f) (g) : functionalCoefficient ds ℓ₁ f g = C f g :=
    (hEval₁ f g).trans (hL₁.1 f g)
  have hMatch₂ (f) (g) : functionalCoefficient ds ℓ₂ f g = B f g :=
    (hEval₂ f g).trans (hL₂.1 f g)
  have hℓ₁ : ℓ₁ ≠ 0 := by
    intro he
    apply hCne
    ext1 f
    funext g
    rw [← hMatch₁, he]
    rfl
  obtain ⟨c, hc⟩ := hasSmoothWhittakerUniqueness_of_map_character cs hr a
    ℓ₁ ℓ₂ hBound₁ hBound₂ hCov₁ hCov₂ hℓ₁
  refine ⟨c, LinearMap.ext fun f => funext fun g => ?_⟩
  change B f g = c * C f g
  rw [← hMatch₁, ← hMatch₂, hc]
  rfl

/-- A nonzero original block model contains the entire ascending Whittaker model. -/
theorem uniformModel_ascendingExpand_le_of_ne_bot (r : ℕ) (ds : List RealBlock)
    (hr : realRank ds = r + 1) (a : ℝˣ) (hW : realWhittakerModel r ds a ≠ ⊥) :
    realUniformWhittakerModel r (ascendingExpand ds) a ≤ realWhittakerModel r ds a := by
  have he := (realRank_ascendingExpand ds).trans hr
  rw [← realWhittakerModels_eq r (ascendingExpand ds) he a]
  exact realAscendingWhittakerDescentFromMultiplicity r ds hr a
    (realExactCharacterWhittakerUniqueness r (ascendingCharacters ds) he a) hW

end Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries
