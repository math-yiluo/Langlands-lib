import Langlands.Representation.Classification.RelativeGenericJacquetTotalsProof
import Langlands.Representation.Classification.RelativeJacquetEqualTotalsComparisonProof
import Langlands.Representation.Classification.RelativeInnerJacquetPositiveQuotientProof
import Langlands.Representation.Classification.RelativePositiveTotalHeadProof
import Langlands.Representation.CuspidalSupport.RefinedCuspidalInductionReduction
import Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionLengthProof
import Langlands.Representation.Parabolic.InductionFactorMatchingProof
import Langlands.Representation.Exponents.UnitaryDualJacquetSupportAdapters

/-! Generic constituent Jacquet comparison and its irreducible head consequence. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV uW

/-- Actual inner and ambient Jacquet counts agree for each irreducible
admissible constituent, and positivity detects inner quotients. -/
theorem glRelativeGenericJacquetMultiplicity :
    GLRelativeGenericJacquetMultiplicityStatement.{uF, uV, uW} := by
  intro p _ F T
  let := T.topology
  intro n hn B S ω hωi hωc hωu v₀ t ht τ I μ hμi hμa hsub
  let := T.leviTopologicalGroup B
  let α := Rep.of (T.leviRealPowerTwist (B.flatten S)
    (fun k => -v₀ k + t ((B.flattenBlockEquiv S).symm k).1) ω.ρ)
  have hαi : Representation.IsIrreducible α.ρ :=
    (T.isIrreducible_leviRealPowerTwist_iff (B.flatten S) _ ω.ρ).mpr hωi
  have hαc : CuspidalSupport.IsLeviCuspidal (B.flatten S) α.ρ :=
    (T.isLeviCuspidal_leviRealPowerTwist_iff (B.flatten S) _ ω.ρ).mpr hωc
  obtain ⟨hIa, _hIfinite, l, s, hs⟩ :=
    CuspidalSupport.refinedCuspidalInductionFiniteLength_of_cuspidalInductionLength
      F T (CuspidalSupport.cuspidalInductionLength.{uF, uV} F T n) B S α hαi hαc
  have had : ∀ i : Fin l, IsAdmissible (s.gradedRepresentation i).ρ := by
    intro i
    have hu : IsAdmissible (s.subrepresentation i.succ).toRepresentation :=
      isAdmissible_of_injective
        { toLinearMap := (s.subrepresentation i.succ).toSubmodule.subtype
          isIntertwining' := fun _ => rfl }
        Subtype.val_injective hIa
    exact Unramified.SphericalExistence.isAdmissible_of_surjective
      (UnitaryDualJacquetSupport.levi_compactOpen_cofinal T B)
      (s.gradedProjection i).hom (s.gradedProjection_surjective i) hu
  obtain ⟨hin, hout⟩ := glRelativeGenericJacquetTotals.{uF, uV}
    p F T n hn B S ω hωi hωc hωu v₀ t ht
  obtain ⟨m, hm, ha⟩ :=
    glRelativeJacquetEqualTotalsComparison.{uF, max uF uV, uV, uW}
      p F T n hn B S I hIa.1 l s hs had τ _ hin hout μ hμi hμa hsub
  exact ⟨m, hm, ha,
    glRelativeInnerJacquetPositiveQuotient.{uF, uV, uW}
      p F T n hn B S ω hωi hωc v₀ t μ hμi hμa m hm⟩

/-- The outer induction of a generic inner quotient has an irreducible
quotient, and all irreducible quotient maps have the same kernel. -/
theorem glRelativeGenericHead :
    GLRelativeGenericHeadStatement.{uF, uV, uW} := by
  have hcomp := glRelativeGenericJacquetMultiplicity.{uF, uV, uW}
  intro p _ F T
  let := T.topology
  intro n hn B S ω hωi hωc hωu v₀ t ht τ I μ hμi hμa hquot
  let := T.leviTopologicalGroup B
  let := T.generalLinearTopologicalGroup n
  obtain ⟨q, hq⟩ := hquot
  let i : (⊤ : Subrepresentation I.ρ).toRepresentation.IntertwiningMap I.ρ :=
    { toLinearMap := (⊤ : Subrepresentation I.ρ).toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  have hsub : ∃ U : Subrepresentation I.ρ,
      ∃ f : U.toRepresentation.IntertwiningMap μ.ρ, Function.Surjective f := by
    refine ⟨⊤, q.comp i, fun w => ?_⟩
    obtain ⟨v, hv⟩ := hq w
    exact ⟨⟨v, trivial⟩, hv⟩
  obtain ⟨m, hm, ha, hpos⟩ :=
    hcomp p F T n hn B S ω hωi hωc hωu v₀ t ht μ hμi hμa hsub
  let α := Rep.of (T.leviRealPowerTwist (B.flatten S)
    (fun k => -v₀ k + t ((B.flattenBlockEquiv S).symm k).1) ω.ρ)
  have hαi : Representation.IsIrreducible α.ρ :=
    (T.isIrreducible_leviRealPowerTwist_iff (B.flatten S) _ ω.ρ).mpr hωi
  have hαc : CuspidalSupport.IsLeviCuspidal (B.flatten S) α.ρ :=
    (T.isLeviCuspidal_leviRealPowerTwist_iff (B.flatten S) _ ω.ρ).mpr hωc
  have hfull := CuspidalSupport.normalizedParabolicInduced_refined_finiteLength
    F T (CuspidalSupport.cuspidalInductionLength.{uF, uV} F T n) B S α hαi hαc
  have hIndq : Function.Surjective (T.normalizedParabolicInducedMap B q) :=
    Parabolic.normalizedInducedSurjectivity_of_smoothInductionSurjectivity T B
      Induction.smoothInductionSurjectivity _ _ _ _ q
      (T.isSmooth_normalizedRefinedInduced B S τ.ρ) hμa.1 hq
  have hfinite : IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      (CuspidalJacquetMultiplicity.induced T B μ).ρ.asModule :=
    FiniteLengthAssembly.finiteLength_of_surjective
      (T.normalizedParabolicInducedMap B q) hIndq hfull
  exact glRelativePositiveTotalHead.{uF, uV, uW}
    p F T n hn B S τ μ hμi hμa hfinite m (hpos.mpr ⟨q, hq⟩) hm ha

/-- Generic constituent comparison and the strong irreducible head consequence,
with independent field, fine-carrier and constituent universes. -/
theorem glRelativeGenericComparison :
    GLRelativeGenericComparisonStatement.{uF, uV, uW} :=
  ⟨glRelativeGenericJacquetMultiplicity.{uF, uV, uW},
    glRelativeGenericHead.{uF, uV, uW}⟩

end Langlands
