import Langlands.Global.RankinSelberg.ComplexOrdinaryEqualAdjacentGeneration
import Langlands.Global.RankinSelberg.ComplexOrdinaryGapCoverage
import Langlands.Global.RankinSelberg.ComplexOrdinaryStandardGeneration
import Langlands.Representation.Archimedean.ComplexStandardIrreducibilityInStages

/-! # Complex ordinary Rankin–Selberg normalized generation -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal Langlands.Archimedean Langlands.LocalFactor.Archimedean
open ComplexGapRankCoordinates (rankLT)

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem complexOrdinaryUnequalStandardCover (t q : ℕ) :
    ∀ (ds es : List ComplexCharacterData), ds.length = t + 1 + q + 1 → es.length = t + 1 →
    IsIrreducibleGKModule (complexStandardRep (t + 1 + q + 1) ds) (complexStandardLie (t + 1 + q + 1) ds) →
    IsIrreducibleGKModule (complexStandardRep (t + 1) es) (complexStandardLie (t + 1) es) →
    ∀ D : ComplexQuotientMeasureData t,
      HasCoveringOrdinaryNormalizations (complexOrdinaryUnequalTest (rankLT t q) ds es 1 D)
        (complexPairLFactor ds es) := by
  induction q with
  | zero =>
      intro ds es hd he hId hIe D
      exact ((complexOrdinaryEqualAdjacentGeneration t 1 (by simp)).2 ds es hd he hId hIe D).covering
  | succ q ih =>
      intro ds es hd he hId hIe D
      cases ds with
      | nil => simp at hd
      | cons d ds =>
          have hds : ds.length = t + 1 + q + 1 := Nat.succ.inj hd
          have hRet := complexStandardIrreducible_of_sublist hd (List.sublist_cons_self d ds) hId
          rw [hds] at hRet
          have hLift := complexOrdinaryGapCoverage t q (-1) (by simp) d ds es hds he hId hIe D
          rw [neg_neg] at hLift
          exact hLift (ih ds es hds he hRet hIe D)

/-- Complex ordinary Rankin–Selberg normalized values cover every spectral point, with finite
unit sums in equal and adjacent ranks at both standard signs. -/
theorem complexOrdinaryNormalizedGeneration : ComplexOrdinaryNormalizedGenerationStatement := by
  apply complexOrdinaryStandardGenerationReduction
  constructor
  · intro r t h ds es hd he hId hIe D _ _
    refine ⟨?_, ?_⟩
    · obtain ⟨q, rfl⟩ : ∃ q : ℕ, r = t + 1 + q := ⟨r - (t + 1), by omega⟩
      exact complexOrdinaryUnequalStandardCover t q ds es hd he hId hIe D
    · rintro rfl
      exact (complexOrdinaryEqualAdjacentGeneration t 1 (by simp)).2 ds es hd he hId hIe D
  · intro r ds es hd he hId hIe D _ _
    exact (complexOrdinaryEqualAdjacentGeneration r 1 (by simp)).1 ds es hd he hId hIe D

end Langlands.Global.RankinSelbergGlobal
