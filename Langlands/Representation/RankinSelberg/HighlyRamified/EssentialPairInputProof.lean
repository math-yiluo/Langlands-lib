import Langlands.Representation.RankinSelberg.HighlyRamified.EssentialLevel
import Langlands.Representation.RankinSelberg.HighlyRamified.UnitaryGamma

/-!
# The essential pair input

The essential pair input `EssentialPairInput n` follows from the uniform rank-one statement
alone: the gamma factors of a highly ramified twist against norm-one unramified principal
series are monomials (`exists_bound_principalSeriesGamma`), and this puts the zero-cell
Kirillov lift at the expected level (`exists_levelFixed_zeroCellLift_of_unit_gamma`).
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV

/-- The essential pair input from the uniform rank-one statement: `ξ` has conductor at
least the bound of `exists_bound_principalSeriesGamma` and at least `1`, and
`f = (n + 3) a(ξ)`. -/
theorem essentialPairInput_of_uniformRankOne (h3 : UniformRankOneTwistStatement.{uF, uV})
    (n : ℕ) : EssentialPairInput.{uF, uV} n := by
  intro p _ F ψ hψ0 m
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  obtain ⟨ν⟩ := nonempty_selfDualHaar F ψ
  obtain ⟨B, hB⟩ := exists_bound_principalSeriesGamma F h3 ψ ν hψ0 n m
  obtain ⟨ξ, hξ⟩ := padicQuasicharacterUnboundedConductor p F (max B 1)
  have hψ := hasIntegerConductor_of_additiveConductor_eq_zero F ψ hψ0
  have hξB : B ≤ T.multiplicativeConductor ξ := le_of_max_le_left hξ
  have hξ1 : 0 < T.multiplicativeConductor ξ := lt_of_lt_of_le one_pos (le_of_max_le_right hξ)
  have hf : 0 < (n + 2 + 1) * T.multiplicativeConductor ξ := Nat.mul_pos (by omega) hξ1
  refine ⟨ξ, (n + 2 + 1) * T.multiplicativeConductor ξ, hf, ?_⟩
  intro V₁ V₂ _ _ _ _ π₁ π₂ hπ₁ hπ₂ hl₁ hl₂
  obtain ⟨c₁, hc₁⟩ := hB π₁ hπ₁ hl₁ ξ hξB
  obtain ⟨c₂, hc₂⟩ := hB π₂ hπ₂ hl₂ ξ hξB
  obtain ⟨ℓ₁, hℓ₁, w₁, hw₁, hP₁⟩ := exists_levelFixed_zeroCellLift_of_unit_gamma F ψ hψ ν.val
    _ (isGeneric_quasicharacter_twist T ψ ξ hπ₁) c₁ _ (fun z _ => hc₁ z)
  obtain ⟨ℓ₂, hℓ₂, w₂, hw₂, hP₂⟩ := exists_levelFixed_zeroCellLift_of_unit_gamma F ψ hψ ν.val
    _ (isGeneric_quasicharacter_twist T ψ ξ hπ₂) c₂ _ (fun z _ => hc₂ z)
  have h1 : ∀ j : Fin (n + 2 + 1),
      (1 : Langlands.GeneralLinear (n + 2 + 1) F.Carrier).val (Fin.last (n + 2)) j =
        if j = Fin.last (n + 2) then 1 else 0 := by
    intro j
    simp [Matrix.one_apply, eq_comm]
  have hw₁1 : w₁.val.val 1 = 1 := by rw [hP₁ 1 h1, zeroCellWhittaker_one]
  have hw₂1 : w₂.val.val 1 = 1 := by rw [hP₂ 1 h1, zeroCellWhittaker_one]
  exact ⟨ℓ₁, ℓ₂, hℓ₁, hℓ₂, w₁, w₂, hw₁, hw₂,
    fun g hg => (hP₁ g hg).trans (hP₂ g hg).symm, hw₁1, hw₂1,
    fun _ hω => trivialOnPrincipalUnits_of_levelFixed hf w₁ hw₁ hw₁1 hω,
    fun _ hω => trivialOnPrincipalUnits_of_levelFixed hf w₂ hw₂ hw₂1 hω⟩

end Langlands.RankinSelberg.HighlyRamified
