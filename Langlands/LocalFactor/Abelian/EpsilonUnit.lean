import Langlands.LocalFactor.PadicAbelianLocalAnalysisProof
import Langlands.HarmonicAnalysis.CharacterTransport
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Units and Haar-independent ratios of actual abelian epsilon expressions -/

noncomputable section

open MeasureTheory

namespace Langlands.PadicField.TopologicalData

open LocalFactor.PadicAbelian

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology
local notation "FieldCharacter" =>
  @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology
    (@borel F.Carrier T.topology)

/-- Tate's proved nonvanishing applies to the original integral expression. -/
theorem abelianEpsilonExpression_ne_zero (χ : FieldCharacter)
    (ψ : AdditiveCharacter) (μ : LocalHaar) :
    T.abelianEpsilonExpression χ ψ μ ≠ 0 := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  rw [← deligneConstant_eq_abelianEpsilonExpression T χ ψ μ]
  exact epsilonAt_ne_zero T (uniformizerUnit T) χ
    ((conductorAt_iff T χ _).mpr rfl) ψ (T.additiveConductor ψ) μ
    ((additiveConductorAt_iff T ψ _).mpr rfl) 0

/-- The existing abelian expression, now regarded as a complex unit using the
proved nonvanishing theorem. -/
def abelianEpsilonUnit (χ : FieldCharacter)
    (ψ : AdditiveCharacter) (μ : LocalHaar) : ℂˣ :=
  Units.mk0 (T.abelianEpsilonExpression χ ψ μ)
    (T.abelianEpsilonExpression_ne_zero χ ψ μ)

@[simp]
theorem coe_abelianEpsilonUnit (χ : FieldCharacter)
    (ψ : AdditiveCharacter) (μ : LocalHaar) :
    (T.abelianEpsilonUnit χ ψ μ : ℂ) = T.abelianEpsilonExpression χ ψ μ := rfl

/-- Scaling the original Haar measure scales the original integral expression. -/
theorem abelianEpsilonExpression_haarScale (χ : FieldCharacter)
    (ψ : AdditiveCharacter) (μ : LocalHaar) (c : NNReal) (hc : 0 < c) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    T.abelianEpsilonExpression χ ψ (μ.scale c hc) =
      (c : ℂ) * T.abelianEpsilonExpression χ ψ μ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  rw [← deligneConstant_eq_abelianEpsilonExpression T χ ψ (μ.scale c hc),
    ← deligneConstant_eq_abelianEpsilonExpression T χ ψ μ]
  exact epsilonAt_smul_measure T (uniformizerUnit T) χ ψ.toAddChar μ.measure
    (T.multiplicativeConductor χ) (T.additiveConductor ψ) c 0

/-- The same positive Haar scaling identity in the group of complex units. -/
theorem abelianEpsilonUnit_haarScale (χ : FieldCharacter)
    (ψ : AdditiveCharacter) (μ : LocalHaar) (c : NNReal) (hc : 0 < c) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    T.abelianEpsilonUnit χ ψ (μ.scale c hc) =
      Units.mk0 (c : ℂ) (by exact_mod_cast (ne_of_gt hc)) *
        T.abelianEpsilonUnit χ ψ μ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  apply Units.ext
  exact T.abelianEpsilonExpression_haarScale χ ψ μ c hc

/-- The epsilon ratio attached to a difference of two character lines. -/
def abelianEpsilonRatio (χ χ' : FieldCharacter)
    (ψ : AdditiveCharacter) (μ : LocalHaar) : ℂˣ :=
  T.abelianEpsilonUnit χ ψ μ / T.abelianEpsilonUnit χ' ψ μ

/-- A difference of character lines has degree zero, so its abelian epsilon
ratio is unchanged by every positive Haar scaling. -/
theorem abelianEpsilonRatio_haarScale (χ χ' : FieldCharacter)
    (ψ : AdditiveCharacter) (μ : LocalHaar) (c : NNReal) (hc : 0 < c) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    T.abelianEpsilonRatio χ χ' ψ (μ.scale c hc) =
      T.abelianEpsilonRatio χ χ' ψ μ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  simp only [abelianEpsilonRatio, T.abelianEpsilonUnit_haarScale, mul_div_mul_left_eq_div]

/-- The ratio is independent of the supplied regular additive Haar measure. -/
theorem abelianEpsilonRatio_haarIndependent (χ χ' : FieldCharacter)
    (ψ : AdditiveCharacter) (μ ν : LocalHaar) :
    T.abelianEpsilonRatio χ χ' ψ μ = T.abelianEpsilonRatio χ χ' ψ ν := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let c := Measure.addHaarScalarFactor μ.measure ν.measure
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hm : μ.measure = (ν.scale c hc).measure := by
    exact Measure.isAddLeftInvariant_eq_smul_of_regular μ.measure ν.measure
  have hext (a b : LocalHaar) (h : a.measure = b.measure) : a = b := by
    cases a
    cases b
    cases h
    rfl
  have hμ : μ = ν.scale c hc := hext μ (ν.scale c hc) hm
  rw [hμ, T.abelianEpsilonRatio_haarScale]

end Langlands.PadicField.TopologicalData
