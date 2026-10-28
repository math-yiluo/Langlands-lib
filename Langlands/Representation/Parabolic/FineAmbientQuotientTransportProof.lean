import Langlands.Representation.Parabolic.FineAmbientQuotientTransportStatement
import Langlands.Representation.Parabolic.RefinedLeviRealTwistProof
import Langlands.Representation.Parabolic.OrderedRefinementInduction
import Langlands.Representation.Parabolic.ComposedFlattenedInductionProof
import Langlands.Representation.Parabolic.InductionFactorMatchingProof

/-! Actual fine-to-ambient transport of specified quotient maps. -/

noncomputable section

set_option maxHeartbeats 800000

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity Parabolic

universe uF uV uW uZ

/-- Actual fine ambient induction surjects onto the given outer quotient. -/
theorem fineAmbientQuotientTransport :
    FineAmbientQuotientTransportStatement.{uF, uV, uW, uZ} := by
  intro p _ F T
  let := T.topology
  intro n B S ω hω v₀ t π q₀ hq₀ J q hq
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  have hπ : IsSmooth π.ρ :=
    isSmooth_of_surjective q₀ hq₀
      (T.isSmooth_normalizedRefinedInduced B S (fineTwist T B S ω v₀ 0).ρ)
  obtain ⟨_, _, _, ht⟩ := (refinedLeviRealTwist p F T n B S ω v₀ t).2
  obtain ⟨qₜ, hqₜ, _⟩ := ht π q₀ hq₀
  let iq := T.normalizedParabolicInducedMap B qₜ
  have hiq : Function.Surjective iq :=
    normalizedInducedSurjectivity_of_smoothInductionSurjectivity T B
      Induction.smoothInductionSurjectivity _ _ _ _ qₜ
      (T.isSmooth_normalizedRefinedInduced B S (fineTwist T B S ω v₀ t).ρ)
      ((T.isSmooth_leviRealPowerTwist_iff B t π.ρ).mpr hπ) hqₜ
  let α := T.leviRealPowerTwist (B.flatten S)
    (fun k => -v₀ k + t ((B.flattenBlockEquiv S).symm k).1) ω.ρ
  have hα : IsSmooth α :=
    (T.isSmooth_leviRealPowerTwist_iff (B.flatten S) _ ω.ρ).mpr hω
  let e := B.flattenBlockEquiv S
  let hs := fun a => (B.flatten_size_flattenBlockEquiv S a).symm
  have hc : ∀ i k x, B.index i ((S i).index k x) =
      (B.flatten S).index (e ⟨i, k⟩) (Fin.cast (hs ⟨i, k⟩) x) :=
    fun i k x => B.index_index_eq_flatten S ⟨i, k⟩ x
  have E := orderedRefinementInductionEquiv F T (B.flatten S) B S e hs hc α hα
  dsimp only [orderedRefinementIteratedInduced] at E
  rw [show (B.flatten S).leviRefinementEquiv B S e hs F.Carrier =
    flattenedLeviEquiv F.Carrier B S from B.leviRefinementEquiv_flatten F.Carrier S] at E
  refine ⟨q.comp (iq.comp E.symm.toIntertwiningMap), ?_⟩
  exact hq.comp (hiq.comp E.symm.surjective)


end Langlands
