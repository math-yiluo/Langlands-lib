import Langlands.Representation.RankinSelberg.InducedTailIntermediateIntegralAssembly
import Langlands.Representation.RankinSelberg.InducedTailIntermediateCharacterTransport
import Langlands.Representation.RankinSelberg.InducedTailIntermediateCoefficientAdapters

/-! # Reversed zero-row tail integrability and continuation -/

noncomputable section

namespace Langlands.RankinSelberg.InducedTailIntermediate

open GeneralLinear MeasureTheory Whittaker HarmonicAnalysis

universe uF uV uW

section RectangularZeroRows

variable {F : Type uF} [Field F] [TopologicalSpace F] [MeasurableSpace F]
variable (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
variable {n : ℕ} (k : ℕ) [MeasurableSpace (LeftUnipotentQuotient n F)]
variable (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
variable (W : WhittakerFunctions ψ (n + (0 + k + 1))) (W' : InverseWhittakerFunctions ψ n)

/-- With the zero-row rectangular measure, absolute convergence is
integrability of the quotient integrand at the unique zero matrix. -/
theorem unequalRankConverges_rectangular_zero_rows_iff (s : ℂ) :
    UnequalRankConverges ψ abv 0 k μ (rectangularMeasure ν 0 (n + 1)) W W' s ↔
      Integrable (unequalRankIntegrand ψ abv 0 k W W' s 0) μ := by
  rw [rectangularMeasure_zero_rows]
  exact unequalRankConverges_zero_rows_iff ψ abv k μ W W' s

/-- With the zero-row rectangular measure, the iterated integral is the
quotient integral at the unique zero matrix, as a function of `s`. -/
theorem unequalRankIntegral_rectangular_zero_rows :
    unequalRankIntegral ψ abv 0 k μ (rectangularMeasure ν 0 (n + 1)) W W' =
      fun s => ∫ x, unequalRankIntegrand ψ abv 0 k W W' s 0 x ∂μ := by
  funext s
  rw [rectangularMeasure_zero_rows]
  exact unequalRankIntegral_zero_rows ψ abv k μ W W' s

/-- The rational continuation of the zero-row iterated integral is the
rational continuation of the quotient integral, with the same function `R`. -/
theorem unequalRankContinuation_rectangular_zero_rows_iff (R : RationalFunctions) :
    HasRationalContinuation q
        (unequalRankIntegral ψ abv 0 k μ (rectangularMeasure ν 0 (n + 1)) W W') R ↔
      HasRationalContinuation q
        (fun s => ∫ x, unequalRankIntegrand ψ abv 0 k W W' s 0 x ∂μ) R := by
  rw [unequalRankIntegral_rectangular_zero_rows]

end RectangularZeroRows

section RankCast

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable (ψ : UnitaryAdditiveCharacter F)

/-- Two successive rank transports of an inverse coefficient are one transport. -/
theorem inverseWhittakerRankCast_trans {l m n : ℕ} (h₁ : l = m) (h₂ : m = n)
    (W : InverseWhittakerFunctions ψ l) :
    inverseWhittakerRankCast ψ h₂ (inverseWhittakerRankCast ψ h₁ W) =
      inverseWhittakerRankCast ψ (h₁.trans h₂) W := by
  subst h₁
  subst h₂
  rfl

end RankCast

section ReversedTail

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
variable (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
variable {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
variable (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {E : Type uW} [AddCommGroup E] [Module ℂ E]

/-- A zero-row value at the inverse character supplies the reversed tail data.
The large coefficient becomes an actual inverse coefficient of the large
representation, transported to rank `m`, and the small coefficient becomes an
actual standard coefficient of the small representation. Their reversed
zero-row integrand is integrable on the same half-plane, and its quotient
integral has the same rational continuation. -/
theorem exists_reversedTail_of_mem_scaled {r m : ℕ} (k : ℕ)
    (hm : r = m) (hk : m = n + (0 + k + 1))
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) E)
    {R : RationalFunctions}
    (hR : R ∈ unequalRankZetaValuesAt 0 k (hm.trans hk) q (ψ.scale (-1)) abv μ
      (rectangularMeasure ν 0 (n + 1)) σ τ) :
    ∃ Wtest ∈ inverseWhittakerSet ψ m (hm ▸ σ), ∃ Wtail ∈ whittakerSet ψ n τ,
      ∃ a : ℝ,
        (∀ s : ℂ, a < s.re → Integrable
          (unequalRankIntegrand (ψ.scale (-1)) abv 0 k
            (inverseAsScaledStandard ψ (inverseWhittakerRankCast ψ hk Wtest))
            (standardAsScaledInverse ψ Wtail) s 0) μ) ∧
        HasRationalContinuation q
          (fun s => ∫ x, unequalRankIntegrand (ψ.scale (-1)) abv 0 k
            (inverseAsScaledStandard ψ (inverseWhittakerRankCast ψ hk Wtest))
            (standardAsScaledInverse ψ Wtail) s 0 x ∂μ) R := by
  subst hm
  subst hk
  obtain ⟨Wf, hWf, W', hW', ⟨a, hconv⟩, hcont⟩ := hR
  refine ⟨scaledStandardAsInverse ψ Wf, scaledStandardAsInverse_mem ψ σ hWf,
    scaledInverseAsStandard ψ W', scaledInverseAsStandard_mem ψ τ hW', a, ?_, ?_⟩
  · intro s hs
    exact (unequalRankConverges_rectangular_zero_rows_iff (ψ.scale (-1)) abv k μ ν
      Wf W' s).1 (hconv s hs)
  · exact (unequalRankContinuation_rectangular_zero_rows_iff q (ψ.scale (-1)) abv k μ ν
      Wf W' R).1 hcont

end ReversedTail

section Compatible

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{uF} p} (T : K.TopologicalData)

/-- With the supplied p-adic topology and a compatible quotient measure, a
zero-row value at the original character supplies the reversed tail data of
`exists_reversedTail_of_mem_scaled` for the same quotient measure. The
inverse-character step is `unequalRankZetaValuesAt_scale_neg_one_compatible`. -/
theorem exists_reversedTail_of_mem_compatible (n r m k : ℕ)
    (hm : r = m) (hk : m = n + (0 + k + 1)) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel K.Carrier
    letI : BorelSpace K.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) K.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n K.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter K.Carrier)
      (ν : AdditiveHaarMeasure K.Carrier)
      (μ : Measure (LeftUnipotentQuotient n K.Carrier)),
      QuotientIntegration.IsCompatible (upperUnipotent (n + 1) K.Carrier)
        (generalLinearHaar K.Carrier n) (unipotentHaar K.Carrier n) μ →
      ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
        {E : Type uW} [AddCommGroup E] [Module ℂ E]
        (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V)
        (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) E)
        (R : RationalFunctions),
        R ∈ unequalRankZetaValuesAt 0 k (hm.trans hk) T.residueCardinality ψ
          (normalizedAbsoluteValue T) μ (rectangularMeasure ν 0 (n + 1)) σ τ →
        ∃ Wtest ∈ inverseWhittakerSet ψ m (hm ▸ σ), ∃ Wtail ∈ whittakerSet ψ n τ,
          ∃ a : ℝ,
            (∀ s : ℂ, a < s.re → Integrable
              (unequalRankIntegrand (ψ.scale (-1)) (normalizedAbsoluteValue T) 0 k
                (inverseAsScaledStandard ψ (inverseWhittakerRankCast ψ hk Wtest))
                (standardAsScaledInverse ψ Wtail) s 0) μ) ∧
            HasRationalContinuation T.residueCardinality
              (fun s => ∫ x, unequalRankIntegrand (ψ.scale (-1))
                (normalizedAbsoluteValue T) 0 k
                (inverseAsScaledStandard ψ (inverseWhittakerRankCast ψ hk Wtest))
                (standardAsScaledInverse ψ Wtail) s 0 x ∂μ) R := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel K.Carrier
  let : BorelSpace K.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
  intro ψ ν μ hμ V _ _ E _ _ σ τ R hR
  rw [unequalRankZetaValuesAt_scale_neg_one_compatible T n r 0 k (hm.trans hk)
    ψ ν μ μ hμ hμ σ τ] at hR
  exact exists_reversedTail_of_mem_scaled T.residueCardinality ψ
    (normalizedAbsoluteValue T) μ ν k hm hk σ τ hR

end Compatible

end Langlands.RankinSelberg.InducedTailIntermediate
