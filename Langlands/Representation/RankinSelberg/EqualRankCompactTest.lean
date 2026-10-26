import Langlands.Representation.RankinSelberg.EqualRankCompactAssembly
import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.Representation.Whittaker.MirabolicUnitTestProof
import Langlands.Representation.Whittaker.MirabolicUnitTestCompatibility
import Langlands.Representation.Whittaker.ModelKirillovProof
import Langlands.Representation.Whittaker.CoefficientRightStabilizer
import Langlands.Analysis.Local.QuotientMass

/-!
# Existence of compact equal-rank coefficient tests

The compact-test existence predicate uses the actual coefficient images.
Its construction is conditional on canonical Kirillov lifting in the two
independent representation universes.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open scoped NNReal

universe uF uV uW

/-- Actual coefficient vectors and a Schwartz test satisfying the compact
assembly hypotheses, with a compact mirabolic set containing the identity
and a compact open ambient right subgroup. -/
def HasEqualRankCompactTest
    {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ) : Prop :=
  ∃ C : Set (mirabolic n F), IsCompact C ∧ 1 ∈ C ∧
    ∃ J : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
      IsCompact (J : Set (Langlands.GeneralLinear (n + 1) F)) ∧
      ∃ (f : (coefficientModel π ℓ).toSubmodule)
        (f' : (coefficientModel σ ℓ').toSubmodule)
        (Φ : SchwartzBruhat (Fin (n + 1) → F)),
        IsEqualRankCompactTest ψ abv C J.toSubgroup f.val f'.val Φ

section Integration

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)]
  [MeasurableMul (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}
  {μG : Measure (Langlands.GeneralLinear (n + 1) F)}
  {μN : Measure (upperUnipotent (n + 1) F)} [μN.IsMulRightInvariant]
  {μ : Measure (LeftUnipotentQuotient n F)}

/-- Compact coefficient tests give rational value one for every compatible
quotient measure. Positivity and finiteness follow from compatibility. -/
theorem HasEqualRankCompactTest.one_mem_equalRankRationalValues
    (h : HasEqualRankCompactTest ψ abv π σ ℓ ℓ')
    (hμ : IsCompatible (upperUnipotent (n + 1) F) μG μN μ) (q : ℕ) :
    (1 : RationalFunctions) ∈ equalRankRationalValues q ψ abv μ π σ ℓ ℓ' := by
  obtain ⟨C, hC, hC1, J, hJ, f, f', Φ, htest⟩ := h
  have hc : IsCompact (equalRankCompactSet C J.toSubgroup) :=
    isCompact_equalRankCompactSet hC hJ
  have ho : IsOpen (equalRankCompactSet C J.toSubgroup) :=
    isOpen_equalRankCompactSet C J
  have hne : (equalRankCompactSet C J.toSubgroup).Nonempty :=
    ⟨leftQuotientMap (upperUnipotent (n + 1) F) 1,
      subgroup_orbit_subset_equalRankCompactSet C J.toSubgroup hC1
        ⟨1, J.one_mem, rfl⟩⟩
  obtain ⟨hpos, hfin⟩ := hμ.measure_pos_lt_top hc ho hne
  exact one_mem_equalRankRationalValues_of_compact_test q ψ abv μ π σ ℓ ℓ'
    f f' Φ C J.toSubgroup htest ho.measurableSet hpos hfin

end Integration

/-- The published mirabolic tests, topology-transfer theorem, common right
stabilizer and row indicator construct actual compact coefficient tests.
Canonical Kirillov remains an explicit premise in each carrier universe. -/
theorem hasEqualRankCompactTest_of_kirillov
    (hV : Langlands.WhittakerTypeKirillovStatement.{uF, uV})
    (hW : Langlands.WhittakerTypeKirillovStatement.{uF, uW})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
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
  obtain ⟨f, hf⟩ := modelKirillovTransfer hV p inferInstance F T n V π ψ
    hπ ℓ hℓ φ hφ
  let ψ' : UnitaryAdditiveCharacter F.Carrier := ψ.scale (-1)
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
  obtain ⟨fneg, hfneg⟩ := modelKirillovTransfer hW p inferInstance F T n W σ ψ'
    hσneg ℓneg hℓ' φneg hφneg
  obtain ⟨v', rfl⟩ := modelMap_surjective σ ℓneg fneg
  let f' := modelMap σ ℓ' v'
  have hf' (g : Langlands.GeneralLinear (n + 1) F.Carrier)
      (hg : ∀ a, g.val (Fin.last n) a = if a = Fin.last n then 1 else 0) :
      f'.val.val g = φ'.val g :=
    hfneg g hg
  obtain ⟨J, hJ, hfix, hJdet⟩ :=
    exists_compactOpen_glCoefficientRightStabilizer F T n ψ V W π σ
      hπ.1.1 hσ.1.1 ℓ ℓ' f f'
  obtain ⟨_hc, _ho, _hne, _hone, ⟨Φ, hΦ⟩, hrow⟩ :=
    lastRowCompactOrbit F T n J hJ
  refine ⟨(P₀ : Set (mirabolic n F.Carrier)), hP₀, P₀.one_mem,
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

end Langlands.RankinSelberg
