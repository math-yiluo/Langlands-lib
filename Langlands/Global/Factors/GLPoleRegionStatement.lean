import Langlands.Representation.RankinSelberg.LocalFactor
import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Classification.Supercuspidal

/-!
# Pole regions of JPSS pair L-polynomials

The `GL_n` half of Henniart 1986, Proposition 4.5(ii), for the actual JPSS
L-polynomial relations of generic irreducible representations over a p-adic field.
The dual pair is `(π^ι, σ^ι)` with `ψ⁻¹`, the pair of the JPSS functional equation.
-/

noncomputable section

universe uF uV uW

namespace Langlands.Global

open MeasureTheory Langlands.HarmonicAnalysis Langlands.Whittaker Langlands.GeneralLinear
open Langlands.RankinSelberg Langlands.QuotientIntegration

namespace GLPoleRegion

/-- `P` and the reflected polynomial `Pdual(q⁻¹ X⁻¹)` have no common nonzero zero. -/
def HasNoReflectedCommonZero (q : ℕ) (P Pdual : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, z ≠ 0 → ¬ (P.eval z = 0 ∧ Pdual.eval ((q : ℂ)⁻¹ * z⁻¹) = 0)

end GLPoleRegion

open GLPoleRegion

section PadicStatements

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Henniart 1986, Proposition 4.5(ii), equal ranks `n + 1`: for generic irreducible
`π` and `σ` that are both essentially tempered, or with `σ` supercuspidal, the JPSS
L-polynomial `P_{π × σ}` and the reflected `P_{π^ι × σ^ι}` have no common zero. -/
def EqualRankPoleRegionStatement (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
        IsGeneric ψ n π → IsGeneric (ψ.scale (-1)) n σ →
        ((T.IsEssentiallyTempered π ∧ T.IsEssentiallyTempered σ) ∨ IsSupercuspidal σ) →
        ∀ P Pdual : Polynomial ℂ,
          IsEqualRankLPolynomial T.residueCardinality ψ (normalizedAbsoluteValue T) μ
            π σ P →
          IsNormalizedGenerator
            (dualEqualRankZetaValues T.residueCardinality ψ (normalizedAbsoluteValue T) μ
              π σ) Pdual →
          HasNoReflectedCommonZero T.residueCardinality P Pdual

/-- Henniart 1986, Proposition 4.5(ii), unequal ranks `n + (j + k + 1) + 1 > n + 1`,
for the JPSS block `j`: for generic irreducible `π` and `σ` that are both essentially
tempered, or of which one is supercuspidal, `P_{π × σ}` and the reflected
`P_{π^ι × σ^ι}` have no common zero. -/
def UnequalRankPoleRegionStatement (n j k : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F.Carrier
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      ∀ ν : AdditiveHaarMeasure F.Carrier,
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ
          (Langlands.GeneralLinear (n + (j + k + 1) + 1) F.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
        IsGeneric ψ (n + (j + k + 1)) π → IsGeneric (ψ.scale (-1)) n σ →
        ((T.IsEssentiallyTempered π ∧ T.IsEssentiallyTempered σ) ∨
          IsSupercuspidal σ ∨ IsSupercuspidal π) →
        ∀ P Pdual : Polynomial ℂ,
          IsUnequalRankLPolynomial T.residueCardinality ψ (normalizedAbsoluteValue T) j k
            μ (rectangularMeasure ν j (n + 1)) π σ P →
          IsNormalizedGenerator
            (dualUnequalRankZetaValues T.residueCardinality ψ (normalizedAbsoluteValue T)
              j k μ (rectangularMeasure ν j (n + 1)) π σ) Pdual →
          HasNoReflectedCommonZero T.residueCardinality P Pdual

end PadicStatements

/-- The `GL_n` pole-region hypotheses of Henniart 1986, Proposition 4.5(ii), over every
p-adic field and realization, in every pair of positive ranks and every JPSS block. -/
def GLPairPoleRegionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    (∀ n, EqualRankPoleRegionStatement.{uF, uV, uW} F T n) ∧
    (∀ n j k, UnequalRankPoleRegionStatement.{uF, uV, uW} F T n j k)

end Langlands.Global
