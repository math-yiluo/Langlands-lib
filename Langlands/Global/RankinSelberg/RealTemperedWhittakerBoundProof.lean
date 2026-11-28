import Langlands.Global.RankinSelberg.RealTemperedWhittakerBound
import Langlands.Global.RankinSelberg.RealSlotBlockData
import Langlands.Global.RankinSelberg.RealDescendingWhittakerRange

/-! # The tempered Whittaker bound in every rank -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open RealLeviStages

/-- **The tempered Whittaker bound.** For every rank-correct real block list with imaginary
exponents, every function of the exact Whittaker model satisfies the half-modulus bound with
arbitrarily small exponential loss, uniformly in the logarithmic diagonal and the orthogonal
factor. -/
theorem realTemperedWhittakerBound : RealTemperedWhittakerBoundStatement := by
  intro r _ ds hr him a W hW ε hε
  obtain ⟨p, z, he⟩ := exists_expand_eq_characterList ds hr
  have h : Automorphic.realStandardKFinite (r + 1) ds ≤
      Automorphic.realStandardKFinite (r + 1) (RealGodementProfiles.characterList p z) :=
    he ▸ RealPrincipalSeries.realStandardKFinite_le_expand (r + 1) ds
  have hW' : W ∈ realWhittakerModel r ds (-(-a)) := by rwa [neg_neg]
  rw [RealPrincipalSeries.realWhittakerModel_eq_range_descendingCanonical r ds hr (-a) p z he h]
    at hW'
  exact temperedBound_of_mem_range ds hr him (-a) p z he h hW' ε hε

end Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker
