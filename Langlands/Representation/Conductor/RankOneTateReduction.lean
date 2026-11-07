import Langlands.Representation.Conductor.RankOneCharacterLevel
import Langlands.Representation.GodementJacquet.LocalTateConductorStatement
import Langlands.Representation.GodementJacquet.TateCharacterReduction

/-! Conditional reduction of the full rank-one conductor clause to scalar Tate theory. -/

noncomputable section

namespace Langlands.Conductor

open GeneralLinear GodementJacquet HarmonicAnalysis RankinSelberg Whittaker MeasureTheory
open GeneralLinear.Iwasawa

universe uF uV

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [T2Space F] [TotallyDisconnectedSpace F]
  [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
  [MeasurableSpace (upperUnipotent 1 F)] [BorelSpace (upperUnipotent 1 F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)] [BorelSpace (LeftUnipotentQuotient 0 F)]
  (q : ℕ) (hq : q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer))
  (abv : AbsoluteValue F ℝ) (ϖ : Fˣ)
  (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)
  (habvϖ : abv (ϖ : F) = (q : ℝ)⁻¹)
  (habvunit : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1)
  (ψ : UnitaryAdditiveCharacter F) (hψ : HasIntegerConductor ψ)
  (ν : AdditiveHaarMeasure F) (hν : IsSelfDual ψ ν)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

include hq hϖ habvϖ habvunit hψ hν

/-- The scalar Tate statement suffices for all rank-one conductor conclusions
on an actual admissible irreducible carrier. -/
theorem exists_rankOneConductor_of_localTate
    (hTate : LocalTateConductorStatement.{uF})
    (π : Representation ℂ (Langlands.GeneralLinear 1 F) V)
    (ha : IsAdmissible π) (hi : π.IsIrreducible) :
    ∃ (c : ℂˣ) (a : ℕ),
      IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, (a : ℤ)) ∧
      IsNewvectorConductor π a ∧ Module.finrank ℂ (levelFixedVectors π a) = 1 := by
  let : MeasurableSpace Fˣ := borel Fˣ
  let : BorelSpace Fˣ := ⟨rfl⟩
  let M := tateCharacterModel π ha hi
  obtain ⟨a, hlevel, hmin, hA, hAd, hP, hPd, c, hFE⟩ :=
    hTate F q hq abv ϖ hϖ habvϖ habvunit M.1.toMonoidHom M.1.continuous ψ hψ ν hν
  have hscalar : ScalarTateEpsilonData q ψ abv (localMultiplicativeHaar F) ν
      M.1.toMonoidHom c (a : ℤ) := by
    refine ⟨hA, hAd, _, _, hP, hPd, hFE⟩
  exact ⟨c, a, rankOneConductorConclusion_of_scalar F q ψ abv ν π
    M.1.toMonoidHom M.2 a hlevel hmin c hscalar⟩

/-- Concrete scalar coefficient and natural conductor, with their full pair
relation and actual fixed-space properties, conditional on the scalar theorem. -/
def rankOneTateConductorWitness
    (hTate : LocalTateConductorStatement.{uF})
    (π : Representation ℂ (Langlands.GeneralLinear 1 F) V)
    (ha : IsAdmissible π) (hi : π.IsIrreducible) :
    {w : ℂˣ × ℕ //
      IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (w.1, (w.2 : ℤ)) ∧
      IsNewvectorConductor π w.2 ∧ Module.finrank ℂ (levelFixedVectors π w.2) = 1} := by
  have h := exists_rankOneConductor_of_localTate F q hq abv ϖ hϖ habvϖ habvunit
    ψ hψ ν hν hTate π ha hi
  exact ⟨(Classical.choose h, Classical.choose (Classical.choose_spec h)),
    Classical.choose_spec (Classical.choose_spec h)⟩

/-- The exact rank-one instance of the host conductor conclusion follows from
the scalar statement, without additional measurable or carrier hypotheses. -/
theorem conductorExponent_rankOne_of_localTate
    (hTate : LocalTateConductorStatement.{uF})
    (π : Representation ℂ (Langlands.GeneralLinear 1 F) V)
    (hπ : IsGeneric ψ 0 π) :
    ∃ (c : ℂˣ) (a : ℕ),
      IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, (a : ℤ)) ∧
      IsNewvectorConductor π a ∧ Module.finrank ℂ (levelFixedVectors π a) = 1 :=
  exists_rankOneConductor_of_localTate F q hq abv ϖ hϖ habvϖ habvunit
    ψ hψ ν hν hTate π hπ.2.1 hπ.1

end Langlands.Conductor
