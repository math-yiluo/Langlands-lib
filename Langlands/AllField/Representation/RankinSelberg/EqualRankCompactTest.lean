import Langlands.Representation.RankinSelberg.EqualRankCompactTest
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatementSupplement
import Langlands.AllField.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.AllField.Representation.Whittaker.CoefficientRightStabilizer
import Langlands.AllField.Representation.Whittaker.MirabolicUnitTestProof
import Langlands.AllField.Representation.Whittaker.ModelKirillovProof
/-!
# Existence of compact equal-rank coefficient tests

The compact-test existence predicate uses the actual coefficient images.
Its construction is conditional on canonical Kirillov lifting in the two
independent representation universes.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement hasEqualRankCompactTest_of_kirillov lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement exists_compactOpen_glCoefficientRightStabilizer mirabolicUnitTest modelKirillovTransfer
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open scoped NNReal

universe uF uV uW

section Integration


end Integration

/-- The published mirabolic tests, topology-transfer theorem, common right
stabilizer and row indicator construct actual compact coefficient tests.
Canonical Kirillov remains an explicit premise in each carrier universe. -/
theorem hasEqualRankCompactTest_of_kirillov
    (hV : Langlands.AllField.WhittakerTypeKirillovStatement.{uF, uV})
    (hW : Langlands.AllField.WhittakerTypeKirillovStatement.{uF, uW})
    (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
      IsOfWhittakerType n (standardCharacter ψ n) π →
      IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
      ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
        ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
        HasEqualRankCompactTest ψ (normalizedAbsoluteValue T) π σ ℓ ℓ' := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ'
  obtain ⟨P₀, φ, φ', J₀, hP₀, _hJ₀, hPdet, hJ₀P, hvalues, hzero, hright⟩ :=
    mirabolicUnitTest F T n ψ
  have hφ : IsMirabolicTestFunction ψ n φ :=
    isMirabolicTestFunction_of_compact_mirabolic_support ψ φ P₀.toSubgroup
      hP₀ J₀ hJ₀P (fun g hg => (hzero g hg).1)
      (fun g k => (hright g k).1)
  obtain ⟨f, hf⟩ := modelKirillovTransfer hV F T n V π ψ
    hπ ℓ hℓ φ hφ
  let ψ' : UnitaryAdditiveCharacter F := ψ.scale (-1)
  have hθ : standardCharacter ψ' n = inverseStandardCharacter ψ n :=
    standardCharacter_scale_neg_one ψ n
  let ℓneg : glFunctionals ψ' n σ :=
    ⟨ℓ'.val, by
      simpa only [glFunctionals, hθ] using ℓ'.property⟩
  let φneg : WhittakerFunctions ψ' n :=
    ⟨φ'.val, by
      simpa only [WhittakerFunctions, hθ] using φ'.property⟩
  have hφneg : IsMirabolicTestFunction ψ' n φneg :=
    isMirabolicTestFunction_of_compact_mirabolic_support ψ' φneg P₀.toSubgroup
      hP₀ J₀ hJ₀P (fun g hg => (hzero g hg).2)
      (fun g k => (hright g k).2)
  have hσneg : IsOfWhittakerType n (standardCharacter ψ' n) σ := by
    rw [hθ]
    exact hσ
  obtain ⟨fneg, hfneg⟩ := modelKirillovTransfer hW F T n W σ ψ'
    hσneg ℓneg hℓ' φneg hφneg
  obtain ⟨v', rfl⟩ := modelMap_surjective σ ℓneg fneg
  let f' := modelMap σ ℓ' v'
  have hf' (g : Langlands.GeneralLinear (n + 1) F)
      (hg : ∀ a, g.val (Fin.last n) a = if a = Fin.last n then 1 else 0) :
      f'.val.val g = φ'.val g :=
    hfneg g hg
  obtain ⟨J, hJ, hfix, hJdet⟩ :=
    exists_compactOpen_glCoefficientRightStabilizer F T n ψ V W π σ
      hπ.1.1 hσ.1.1 ℓ ℓ' f f'
  obtain ⟨_hc, _ho, _hne, _hone, ⟨Φ, hΦ⟩, hrow⟩ :=
    lastRowCompactOrbit F T n J hJ
  refine ⟨(P₀ : Set (mirabolic n F)), hP₀, P₀.one_mem,
    J, hJ, f, f', Φ, ?_⟩
  refine ⟨?_, ?_, ?_, hrow, ?_, hJdet⟩
  · intro a
    rw [hf a.val a.property, hf' a.val a.property]
    exact mirabolicTests_product_eq_quotient_indicator ψ φ φ' P₀.toSubgroup
      hvalues hzero a.val
  · intro g j
    rw [hfix.1 g j, hfix.2 g j]
  · intro y
    exact congrFun hΦ y
  · intro c hc
    exact congrArg (fun a : ℝ≥0ˣ => ((a : ℝ≥0) : ℝ)) (hPdet ⟨c, hc⟩)

end Langlands.AllField.RankinSelberg
