import Langlands.Global.Factors.GLPoleRegionStatement
import Langlands.LocalField.Normalization.Proof
import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.RankinSelberg.UnequalRankDualCharacterChange
import Langlands.Representation.RankinSelberg.HighlyRamified.EssentialInput
import Langlands.Representation.RankinSelberg.PairLFactor
import Langlands.Representation.RankinSelberg.PadicGenericDualLFactor

/-!
# Transport lemmas for the GL pole-region statement

Every realization `T` of a p-adic field is its canonical realization; the
unequal-rank L-polynomial relation does not depend on the additive Haar measure
used for the rectangular variable; the L-polynomial relations of the statement
`GLPairPoleRegionStatement` agree with the Library relation
`IsPadicSymmetricLPolynomial`; and no reflected common zero exists when the two
polynomials have large enough zero-free disks.
-/

noncomputable section

namespace Langlands

universe uF uV uW

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear RankinSelberg
  QuotientIntegration Polynomial
open scoped NNReal ENNReal

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- For every realization, `x ≤ᵥ 1` exactly when the canonical norm of `x` is at
most one. -/
theorem vle_one_iff_canonicalNorm_le_one (T : F.TopologicalData) (x : F.Carrier) :
    T.valuativeRel.vle x 1 ↔ F.canonicalNorm x ≤ 1 := by
  rw [T.canonicalNorm_le_one_iff_mem_integers x]
  let := T.valuativeRel
  exact ((ValuativeRel.valuation F.Carrier).vle_one_iff).trans Iff.rfl

/-- Every realization carries the valuative relation of the canonical realization. -/
theorem valuativeRel_eq_canonical (T : F.TopologicalData) :
    T.valuativeRel = F.canonicalTopologicalData.valuativeRel := by
  have key : ∀ x : F.Carrier, T.valuativeRel.vle x 1 ↔
      F.canonicalTopologicalData.valuativeRel.vle x 1 := fun x =>
    (T.vle_one_iff_canonicalNorm_le_one x).trans
      (F.canonicalTopologicalData.vle_one_iff_canonicalNorm_le_one x).symm
  ext x y
  by_cases hy : y = 0
  · subst hy
    exact (@ValuativeRel.vle_zero_iff _ _ T.valuativeRel x).trans
      (@ValuativeRel.vle_zero_iff _ _ F.canonicalTopologicalData.valuativeRel x).symm
  · rw [← @ValuativeRel.div_vle_one_iff _ _ T.valuativeRel x y hy,
      ← @ValuativeRel.div_vle_one_iff _ _ F.canonicalTopologicalData.valuativeRel x y hy]
    exact key (x / y)

/-- Two realizations with the same topology and valuative relation are equal; the
remaining fields are proofs. -/
theorem ext_of_topology_valuativeRel {T₁ T₂ : F.TopologicalData}
    (ht : T₁.topology = T₂.topology) (hv : T₁.valuativeRel = T₂.valuativeRel) : T₁ = T₂ := by
  cases T₁
  cases T₂
  dsimp only at ht hv
  subst ht hv
  rfl

/-- Every realization of a p-adic field is its canonical realization. -/
theorem eq_canonicalTopologicalData (T : F.TopologicalData) :
    T = F.canonicalTopologicalData :=
  ext_of_topology_valuativeRel
    (T.topology_eq_canonicalModule.trans
      F.canonicalTopologicalData.topology_eq_canonicalModule.symm)
    T.valuativeRel_eq_canonical

end PadicField.TopologicalData

namespace RankinSelberg

section RectangularScaling

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)

/-- Rescaling the rectangular measure does not change the Laurent span of the
unequal-rank values. -/
theorem zetaSpan_unequalRankValuesOf_smul_rectangular {n : ℕ} (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    [SFinite ν] {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ∞)
    (S : Set (WhittakerFunctions ψ (n + (j + k + 1))))
    (S' : Set (InverseWhittakerFunctions ψ n)) :
    zetaSpan (unequalRankValuesOf q ψ abv j k μ (c • ν) S S') =
      zetaSpan (unequalRankValuesOf q ψ abv j k μ ν S S') := by
  have hr : ((c.toReal : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hc₀, hc⟩)
  have hconv : ∀ W W' s, UnequalRankConverges ψ abv j k μ (c • ν) W W' s ↔
      UnequalRankConverges ψ abv j k μ ν W W' s := by
    intro W W' s
    rw [UnequalRankConverges, UnequalRankConverges, Measure.prod_smul_right]
    exact integrable_smul_measure hc₀ hc
  have hint : ∀ W W', unequalRankIntegral ψ abv j k μ (c • ν) W W' =
      fun s => ((c.toReal : ℝ) : ℂ) * unequalRankIntegral ψ abv j k μ ν W W' s := by
    intro W W'
    funext s
    simp only [unequalRankIntegral, integral_smul_measure, Complex.real_smul]
    exact integral_const_mul _ _
  refine zetaSpan_eq_of_const_mul (inv_ne_zero hr) ?_ ?_
  · rintro R ⟨W, hW, W', hW', ⟨a, ha⟩, hR⟩
    refine ⟨W, hW, W', hW', ⟨a, fun s hs => (hconv W W' s).1 (ha s hs)⟩, ?_⟩
    have h := hasRationalContinuation_const_mul ((c.toReal : ℝ) : ℂ)⁻¹ hR
    convert h using 1
    funext s
    rw [hint]
    exact (inv_mul_cancel_left₀ hr _).symm
  · rintro R ⟨W, hW, W', hW', ⟨a, ha⟩, hR⟩
    refine ⟨W, hW, W', hW', ⟨a, fun s hs => (hconv W W' s).2 (ha s hs)⟩, ?_⟩
    rw [inv_inv, hint]
    exact hasRationalContinuation_const_mul _ hR

/-- The unequal-rank L-polynomial does not depend on the normalization of the
rectangular measure. -/
theorem isUnequalRankLPolynomial_smul_rectangular {n : ℕ} (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    [SFinite ν] {c : ℝ≥0∞} (hc₀ : c ≠ 0) (hc : c ≠ ∞)
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) (P : ℂ[X]) :
    IsUnequalRankLPolynomial q ψ abv j k μ (c • ν) π π' P ↔
      IsUnequalRankLPolynomial q ψ abv j k μ ν π π' P :=
  isNormalizedGenerator_congr
    (zetaSpan_unequalRankValuesOf_smul_rectangular q ψ abv j k μ ν hc₀ hc _ _) P

end RectangularScaling

section HaarChange

variable {F : Type uF} [Field F] [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
  [IsTopologicalAddGroup F] [LocallyCompactSpace F] [SigmaCompactSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)

omit [SigmaCompactSpace F] in
/-- Two additive Haar measures differ by a positive finite scalar. -/
theorem AdditiveHaarMeasure.exists_eq_smul (ν ν₀ : AdditiveHaarMeasure F) :
    ∃ κ : ℝ≥0, κ ≠ 0 ∧ ν.measure = κ • ν₀.measure :=
  ⟨Measure.addHaarScalarFactor ν.measure ν₀.measure,
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν.measure ν₀.measure).ne',
    Measure.isAddLeftInvariant_eq_smul_of_regular ν.measure ν₀.measure⟩

/-- The unequal-rank L-polynomial does not depend on the additive Haar measure
whose rectangular product measures the matrix variable. -/
theorem isUnequalRankLPolynomial_rectangular_congr {n : ℕ} (j k : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν ν₀ : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) (P : ℂ[X]) :
    IsUnequalRankLPolynomial q ψ abv j k μ (rectangularMeasure ν j (n + 1)) π π' P ↔
      IsUnequalRankLPolynomial q ψ abv j k μ (rectangularMeasure ν₀ j (n + 1)) π π' P := by
  obtain ⟨κ, hκ, h⟩ := AdditiveHaarMeasure.exists_eq_smul ν ν₀
  rw [rectangularMeasure_eq_smul κ h j (n + 1)]
  have hc₀ : ((κ ^ (j * (n + 1)) : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    simpa using pow_ne_zero (j * (n + 1)) hκ
  have hc : ((κ ^ (j * (n + 1)) : ℝ≥0) : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hsmul : (κ ^ (j * (n + 1))) • rectangularMeasure ν₀ j (n + 1) =
      ((κ ^ (j * (n + 1)) : ℝ≥0) : ℝ≥0∞) • rectangularMeasure ν₀ j (n + 1) := rfl
  rw [hsmul]
  exact isUnequalRankLPolynomial_smul_rectangular q ψ abv j k μ _ hc₀ hc π π' P

end HaarChange

end RankinSelberg

namespace Global.GLPoleRegion

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- In equal rank, a polynomial with the JPSS L-polynomial relation of the
statement at one compatible quotient measure is the p-adic pair L-polynomial. -/
theorem eq_of_isEqualRankLPolynomial
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier}
    {n : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
    {P₀ : ℂ[X]} (h₀ : IsPadicPairLPolynomial F ψ ν π σ P₀) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
      (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      ∀ P : ℂ[X], IsEqualRankLPolynomial F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μ π σ P → P = P₀ := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro _ μ hμ P hP
  exact IsNormalizedGenerator.unique hP (isPairLPolynomial_self.1 (h₀.2 μ hμ))

/-- In unequal rank, a polynomial with the JPSS L-polynomial relation of the
statement at one compatible quotient measure and one additive Haar measure on the
rectangular variable is the p-adic pair L-polynomial, whatever additive Haar
measure that pair relation uses. -/
theorem eq_of_isUnequalRankLPolynomial
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ν₀ : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier}
    {n j k : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
    {P₀ : ℂ[X]} (h₀ : IsPadicPairLPolynomial F ψ ν₀ π σ P₀) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
      (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      ∀ (ν : AdditiveHaarMeasure F.Carrier) (P : ℂ[X]),
        IsUnequalRankLPolynomial F.canonicalTopologicalData.residueCardinality ψ
          (normalizedAbsoluteValue F.canonicalTopologicalData) j k
          μ (rectangularMeasure ν j (n + 1)) π σ P → P = P₀ := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro _ μ hμ ν P hP
  have : SecondCountableTopology F.Carrier := F.canonicalTopologicalData.secondCountableTopology
  have h₁ := (h₀.2 μ hμ).isUnequalRankLPolynomial j k
  rw [← isUnequalRankLPolynomial_rectangular_congr _ ψ _ j k μ ν ν₀] at h₁
  exact IsNormalizedGenerator.unique hP h₁

/-- Equal rank: for `π` generic for `ψ` and `σ` generic for `ψ⁻¹`, polynomials with
the L-polynomial relations of the statement at one compatible quotient measure are
the p-adic pair L-polynomials of `(π, σ)` for `ψ` and of `(π^ι, σ^ι)` for `ψ⁻¹`, at
any additive Haar measures `ν` and `νd`. -/
theorem isPadicPairLPolynomial_of_equalRank
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    (ν νd : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {n : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
    (hπ : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      IsGeneric ψ n π)
    (hσ : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      IsGeneric (ψ.scale (-1)) n σ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
      (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      ∀ P Pdual : ℂ[X],
        IsEqualRankLPolynomial F.canonicalTopologicalData.residueCardinality ψ
          (normalizedAbsoluteValue F.canonicalTopologicalData) μ π σ P →
        IsNormalizedGenerator
          (dualEqualRankZetaValues F.canonicalTopologicalData.residueCardinality ψ
            (normalizedAbsoluteValue F.canonicalTopologicalData) μ π σ) Pdual →
        IsPadicPairLPolynomial F ψ ν π σ P ∧
          IsPadicPairLPolynomial F (ψ.scale (-1)) νd (inverseTransposePullback π)
            (inverseTransposePullback σ) Pdual := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro _ μ hμ P Pd hP hPd
  have hπW := isOfWhittakerType_of_isGeneric F hπ
  have hσW : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ := by
    have h := isOfWhittakerType_of_isGeneric F hσ
    rw [← RankinSelberg.standardCharacter_scale_neg_one ψ n]
    exact h
  have h₀ := padicPairLPolynomial_isPadic F ψ ν π σ le_rfl hπW hσW
  have hd₀ := padicPairLPolynomial_isPadic F (ψ.scale (-1)) νd (inverseTransposePullback π)
    (inverseTransposePullback σ) le_rfl (isOfWhittakerType_firstDual ψ π hπW)
    (isOfWhittakerType_secondDual ψ σ hσW)
  rw [eq_of_isEqualRankLPolynomial h₀ μ hμ P hP, eq_of_isEqualRankLPolynomial hd₀ μ hμ Pd hPd]
  exact ⟨h₀, hd₀⟩

/-- Unequal rank: for `π` generic for `ψ` and `σ` generic for `ψ⁻¹`, polynomials with
the L-polynomial relations of the statement at one compatible quotient measure and
one additive Haar measure on the rectangular variable are the p-adic pair
L-polynomials of `(π, σ)` for `ψ` and of `(π^ι, σ^ι)` for `ψ⁻¹`, at any additive
Haar measures `ν₀` and `νd`. -/
theorem isPadicPairLPolynomial_of_unequalRank
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    (ν₀ νd : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {n j k : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Langlands.GeneralLinear (n + (j + k + 1) + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
    (hπ : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      IsGeneric ψ (n + (j + k + 1)) π)
    (hσ : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      IsGeneric (ψ.scale (-1)) n σ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
      (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      ∀ (ν : AdditiveHaarMeasure F.Carrier) (P Pdual : ℂ[X]),
        IsUnequalRankLPolynomial F.canonicalTopologicalData.residueCardinality ψ
          (normalizedAbsoluteValue F.canonicalTopologicalData) j k
          μ (rectangularMeasure ν j (n + 1)) π σ P →
        IsNormalizedGenerator
          (dualUnequalRankZetaValues F.canonicalTopologicalData.residueCardinality ψ
            (normalizedAbsoluteValue F.canonicalTopologicalData) j k μ
            (rectangularMeasure ν j (n + 1)) π σ) Pdual →
        IsPadicPairLPolynomial F ψ ν₀ π σ P ∧
          IsPadicPairLPolynomial F (ψ.scale (-1)) νd (inverseTransposePullback π)
            (inverseTransposePullback σ) Pdual := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro _ μ hμ ν P Pd hP hPd
  have hnr : n ≤ n + (j + k + 1) := by omega
  have hπW := isOfWhittakerType_of_isGeneric F hπ
  have hσW : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ := by
    have h := isOfWhittakerType_of_isGeneric F hσ
    rw [← RankinSelberg.standardCharacter_scale_neg_one ψ n]
    exact h
  have h₀ := padicPairLPolynomial_isPadic F ψ ν₀ π σ hnr hπW hσW
  have hd₀ := padicPairLPolynomial_isPadic F (ψ.scale (-1)) νd (inverseTransposePullback π)
    (inverseTransposePullback σ) hnr (isOfWhittakerType_firstDual ψ π hπW)
    (isOfWhittakerType_secondDual ψ σ hσW)
  rw [eq_of_isUnequalRankLPolynomial h₀ μ hμ ν P hP,
    eq_of_isUnequalRankLPolynomial hd₀ μ hμ ν Pd hPd]
  exact ⟨h₀, hd₀⟩

/-- Zero-free open disks of radii `R` and `R'` around the origin, for `P` and
`Pdual` respectively, exclude reflected common zeros as soon as `q R R' > 1`. -/
theorem hasNoReflectedCommonZero_of_radii {q : ℕ} {P Pdual : ℂ[X]} {R R' : ℝ}
    (hR' : 0 ≤ R') (hlt : 1 < (q : ℝ) * R * R')
    (hP : ∀ z : ℂ, ‖z‖ < R → P.eval z ≠ 0)
    (hPd : ∀ w : ℂ, ‖w‖ < R' → Pdual.eval w ≠ 0) :
    HasNoReflectedCommonZero q P Pdual := by
  rintro z hz ⟨h₁, h₂⟩
  have hzR : R ≤ ‖z‖ := le_of_not_gt fun h => hP z h h₁
  have hR'z : R' ≤ ‖(q : ℂ)⁻¹ * z⁻¹‖ := le_of_not_gt fun h => hPd _ h h₂
  rw [norm_mul, norm_inv, norm_inv, Complex.norm_natCast] at hR'z
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqz : (q : ℝ) * ‖z‖ * R' ≤ 1 := by
    rcases hq.lt_or_eq with hq' | hq'
    · calc (q : ℝ) * ‖z‖ * R' ≤ q * ‖z‖ * ((q : ℝ)⁻¹ * ‖z‖⁻¹) := by gcongr
        _ = 1 := by field_simp
    · rw [← hq']
      simp
  have : (q : ℝ) * R * R' ≤ q * ‖z‖ * R' := by gcongr
  linarith

end Global.GLPoleRegion

end Langlands
