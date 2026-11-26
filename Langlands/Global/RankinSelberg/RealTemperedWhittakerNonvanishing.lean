import Langlands.Global.RankinSelberg.RealCanonicalWhittakerComparison
import Langlands.Global.RankinSelberg.RealRankTwoWhittakerDescent

/-! # Nonvanishing of the exact real Whittaker models for imaginary exponents -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries

open RealGodement RealGodementProfiles

/-- The compact-finite real block model contains a nonzero Whittaker coefficient at
each nonzero additive scale when every inducing exponent is purely imaginary. -/
def RealTemperedWhittakerModelNonvanishingStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 →
    (∀ d ∈ ds, realBlockExponent d = 0) →
    ∀ a : ℝˣ, realWhittakerModel r ds a ≠ ⊥

/-- Every rank-correct real character list has a nonzero exact Whittaker model. -/
theorem realCharacterWhittakerModel_ne_bot (r : ℕ) (cs : List RealCharacterData)
    (hr : realRank (cs.map RealBlock.character) = r + 1) (a : ℝˣ) :
    realWhittakerModel r (cs.map RealBlock.character) a ≠ ⊥ := by
  obtain ⟨p, z, hList⟩ := exists_characterList_of_map_character cs hr
  rw [hList]
  obtain ⟨f, hf⟩ := realGodementCanonicalNonzero r (-a) p z
  have hm := canonicalJacquetMap_mem_uniformModel (-a) p z f
  have hExact := RealUniformWhittaker.model_le_model (characterList p z) (-(-a)) hm
  rw [neg_neg] at hExact
  intro h
  rw [h] at hExact
  exact hf ((Submodule.mem_bot ℂ).mp hExact)

/-- Every real block list of total rank at most two has a nonzero exact Whittaker model,
for arbitrary inducing exponents. -/
theorem realWhittakerModel_ne_bot_of_index_le_one (r : ℕ) (ds : List RealBlock)
    (hr : realRank ds = r + 1) (h : r ≤ 1) (a : ℝˣ) : realWhittakerModel r ds a ≠ ⊥ := by
  match r with
  | 0 =>
    obtain ⟨c, rfl⟩ := RealRankOneStandardModule.eq_singleton_of_realRank_eq_one ds hr
    exact realCharacterWhittakerModel_ne_bot 0 [c] hr a
  | 1 =>
    rw [← realRankTwoWhittakerDescent ds hr a]
    exact realCharacterWhittakerModel_ne_bot 1 (ascendingCharacters ds)
      ((realRank_ascendingExpand ds).trans hr) a
  | r + 2 => omega

end Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries
