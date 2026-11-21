import Langlands.Global.RankinSelberg.ComplexGapCanonicalGrowth
import Langlands.Global.RankinSelberg.ComplexUnequalGrowthInduction

/-! # From the split monomial comparison to the unequal functional equation -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open ComplexGapCanonicalGrowth (ComplexGapMonomialGrowth complexGapCanonicalGrowth)
open ComplexGapRankCoordinates (rankLT)

private theorem growth_iff_integratingCharacter (r t : ℕ) (h : t < r) :
    ComplexLocalUnequalGrowthAtRanks r t h ↔ ComplexGapCanonicalGrowth.ComplexLocalUnequalGrowthAtRanks r t h := by
  constructor
  · intro hGrowth ds es hd he a D W V hW hV
    exact hGrowth ds es hd he (-a) D W V hW (by simpa only [neg_neg] using hV)
  · intro hGrowth ds es hd he a D W V hW hV
    simpa only [neg_neg] using hGrowth ds es hd he (-a) D W V (by simpa only [neg_neg] using hW) hV

/-- Each gap step only needs the split monomial comparison with the smaller-rank growth theorem. -/
def ComplexGapMonomialGrowthStep : Prop :=
  ∀ t q : ℕ, ComplexGapCanonicalGrowth.ComplexLocalUnequalGrowthAtRanks (t + 1 + q) t (rankLT t q) →
    ComplexGapMonomialGrowth t q

/-- The split monomial comparisons plus the adjacent base imply the exact local theorem. -/
def ComplexUnequalFromMonomialGrowthStatement : Prop :=
  ComplexGapMonomialGrowthStep → ComplexLocalUnequalFunctionalEquationStatement

theorem complexUnequalGrowthGapStep_of_monomialGrowth (hMonomial : ComplexGapMonomialGrowthStep) :
    ComplexUnequalGrowthGapStep := by
  intro r t h hGrowth
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt h)
  have hLower := (growth_iff_integratingCharacter _ _ h).mp hGrowth
  have hUpper := complexGapCanonicalGrowth t q (hMonomial t q hLower)
  exact (growth_iff_integratingCharacter _ _ (Nat.lt_succ_of_lt h)).mpr hUpper

theorem complexUnequalFromMonomialGrowth : ComplexUnequalFromMonomialGrowthStatement :=
  fun hMonomial => complexUnequalGrowthInduction (complexUnequalGrowthGapStep_of_monomialGrowth hMonomial)

end Langlands.Global.RankinSelbergGlobal
