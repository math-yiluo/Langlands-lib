import Langlands.Representation.Classification.SegmentSpecialEssentialSquareIntegrabilityProof
import Langlands.Representation.Classification.ChosenUnitaryNormalizationProof
import Langlands.Representation.Classification.SquareIntegrableUnitarityProof
import Langlands.Representation.Classification.SquareIntegrableLanglandsClassificationReduction
import Langlands.Representation.RankinSelberg.WeightedWhittakerSquareReduction
import Langlands.LocalField.Uniformizer

/-!
# Square-integrability criteria for special representations

Essential square-integrability and a unitary central character force the
normalizing real exponent to vanish. Together with the published invariant-form
normalization theorem this proves both criteria for actual segment quotients.
-/

noncomputable section

open scoped NNReal

namespace Langlands.Classification

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- On a nontrivial carrier of positive rank, a unitary central character removes
the real twist in an essential square-integrability witness. -/
theorem isSquareIntegrable_of_essential_of_unitaryCentralCharacter
    {n : ℕ} (hn : 0 < n)
    {V : Type uW} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    (hρ : T.IsEssentiallySquareIntegrable ρ)
    (c : letI := T.topology; UnitaryCentralCharacter ρ) :
    T.IsSquareIntegrable ρ := by
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  obtain ⟨s, hs⟩ := hρ
  obtain ⟨cs⟩ := Langlands.RankinSelberg.nonempty_unitaryCentralCharacter_of_isSquareIntegrable T hs
  have c0 : UnitaryCentralCharacter
      (realPowerTwist (T.determinantNorm n) (-(0 : ℝ)) ρ) := by
    simpa only [neg_zero, realPowerTwist_zero] using c
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hs0 : s = 0 := by
    apply exponent_eq_of_unitaryCentralCharacter (T.determinantNorm n) cs c0 hv
      (GeneralLinear.scalarToCenter (LocalFactor.PadicAbelian.uniformizerUnit T))
    apply ne_of_lt
    change (((T.determinantNorm n
      (GeneralLinear.scalar (LocalFactor.PadicAbelian.uniformizerUnit T)) : ℝ≥0) : ℝ)) < 1
    rw [T.determinantNorm_scalar]
    change T.normalizedAbs
      (LocalFactor.PadicAbelian.uniformizerUnit T : F.Carrier) ^ n < 1
    rw [LocalFactor.PadicAbelian.uniformizerUnit_coe]
    apply pow_lt_one₀ (T.normalizedAbs_nonneg _)
    · rw [T.normalizedAbs_uniformizer, zpow_neg_one]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast T.residueCardinality_gt_one)
    · exact Nat.ne_of_gt hn
  simpa only [hs0, neg_zero, realPowerTwist_zero] using hs

/-- For every actual special quotient, analytic square-integrability is
equivalent both to unitary central character and to an invariant positive
definite Hermitian form on its original carrier. -/
theorem segmentSpecialSquareIntegrabilityCriterion
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SegmentSpecialSquareIntegrabilityCriterion.{uF, uV} F T := by
  let := T.topology
  intro Δ π hπ
  let hi : Representation.IsIrreducible π.representation := hπ.choose_spec.2.1
  let : Nontrivial π :=
    IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ (GeneralLinear Δ.degree F.Carrier)) π.representation.asModule
  have hess := segmentSpecialEssentialSquareIntegrability.{uF, uV} F T Δ π hπ
  constructor
  · exact ⟨Langlands.RankinSelberg.nonempty_unitaryCentralCharacter_of_isSquareIntegrable T,
      fun ⟨c⟩ => isSquareIntegrable_of_essential_of_unitaryCentralCharacter
        T Δ.degree_pos hess c⟩
  · constructor
    · exact glSquareIntegrableUnitarity.{uF, max uF uV}
        p F T Δ.degree Δ.degree_pos π π.representation hi
    · rintro ⟨form⟩
      let d : UnitaryExponentData (T.determinantNorm Δ.degree) π.representation :=
        ⟨0, by simpa only [neg_zero, realPowerTwist_zero] using form⟩
      have hs := chosenUnitarySquareIntegrability.{uF, uV}
        F T Δ.degree Δ.degree_pos π hi hess d
      simpa only [d, neg_zero, realPowerTwist_zero] using hs

end Langlands.Classification
