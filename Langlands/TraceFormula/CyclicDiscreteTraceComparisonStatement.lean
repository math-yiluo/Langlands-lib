import Langlands.TraceFormula.CyclicNormOneTraceComparisonStatement

/-! # Arthur–Clozel (17.8) with the actual split-centre character -/

noncomputable section

open MeasureTheory
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.BaseChange
open scoped CoordinateLevi.Presentation

variable (F : Type) [Field F] [NumberField F] (n : ℕ)

/-- The span of compact smooth adelic tests with finite left and right compact types at infinity. -/
def fullTraceTestSpace : Submodule ℂ (AdelicGroupPoints F (cyclicBaseGroup F n) → ℂ) :=
  Submodule.span ℂ {f | IsCyclicTraceTest F (AdelicGL F n)
    (GeneralLinearGroupPoints.adelicHomeomorph F n) (adelicInfiniteStandardCompact F n) f}

/-- Translate a full test by a positive scalar and restrict to the actual norm-one points. -/
def positiveScalarTranslate (f : AdelicGroupPoints F (cyclicBaseGroup F n) → ℂ) (a : ℝ) :
    normOneSubgroup F (cyclicBaseGroup F n) → ℂ :=
  fun x => f (positiveScalarPoint F n a * x.val)

/-- The positive-centre average as a test on the actual norm-one subgroup. -/
def normOneCentralAverage (da : Measure ℝ) (χ : UnitarySplitCenterCharacter)
    (f : AdelicGroupPoints F (cyclicBaseGroup F n) → ℂ) :
    normOneSubgroup F (cyclicBaseGroup F n) → ℂ :=
  let e := GeneralLinearGroupPoints.adelicHomeomorph F n
  fun x => cyclicCentralAverage F n da χ (f ∘ e.symm) (e x.val)

/-- The trace of the norm-one central average is the average of traces of the translated
norm-one restrictions, with the supplied unitary positive-centre character. -/
def CyclicCentralAverageTraceStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n → ∀ t : ℝ, 0 ≤ t →
    ∀ (D : DiscreteTraceData F n t), D.IsSpectral →
    ∀ (ν : Measure (normOneSubgroup F (cyclicBaseGroup F n))) [ν.IsHaarMeasure],
    D.HasNormOneDistribution ν →
    ∀ (da : Measure ℝ) [da.IsAddHaarMeasure] (χ : UnitarySplitCenterCharacter)
      (f : fullTraceTestSpace F n),
      let avg := normOneCentralAverage F n da χ f.val
      let translates := positiveScalarTranslate F n f.val
      ∃ (h : ∀ a, Integrable (translates a) ν) (havg : Integrable avg ν),
        (∀ a, translates a ∈ normOneTraceTestSpace F n) ∧ avg ∈ normOneTraceTestSpace F n ∧
        let values := fun a => D.normOneTrace ν (translates a) (h a) *
          (χ.toHom (PositiveRealTorus.expUnit a) : ℂ)
        Integrable values da ∧ D.normOneTrace ν avg havg = ∫ a, values a ∂da

/-- The underlying functions of an associated pair are full adelic tests on both sides.
Translation at upper scalar log `a` pairs with base scalar log `[E:F] a`. -/
def CyclicMatchedCentralTranslateStatement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] (n : ℕ), 0 < n →
    ∀ (σ : E ≃ₐ[F] E), IsCyclicAlgebra σ (Module.finrank F E) →
    ∀ (H : CyclicTraceHaarData F E n) (p : cyclicMatchedTests H.localHaar σ),
      p.val.1 ∈ fullTraceTestSpace F n ∧ p.val.2 ∘ H.transport.toUpper.symm ∈ fullTraceTestSpace E n ∧
      ∀ a : ℝ,
        ( (fun x => p.val.1 (positiveScalarPoint F n ((Module.finrank F E : ℝ) * a) * x)),
          (fun x => p.val.2 (H.transport.toUpper.symm (positiveScalarPoint E n a) * x)) ) ∈
          cyclicMatchedTests H.localHaar σ

variable {F n} {E : Type} [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
variable {H : CyclicTraceHaarData F E n} {σ : E ≃ₐ[F] E} {t : ℝ}

/-- The full adelic comparison with the given base split-centre character and upper norm pullback. -/
def CyclicDiscreteComparisonData.ComparedAtCenter (D : CyclicDiscreteComparisonData H σ t) : Prop :=
  ∀ (χ : UnitarySplitCenterCharacter) (p : cyclicMatchedTests H.localHaar σ),
    let f := normOneCentralAverage F n (cyclicBaseCenterMeasure F E n) χ p.val.1
    let φ := normOneCentralAverage E n (cyclicUpperCenterMeasure E n)
      (χ.normPullback (Module.finrank F E)) (p.val.2 ∘ H.transport.toUpper.symm)
    ∃ (hf : Integrable f H.baseNormOne) (hφ : Integrable φ H.upperNormOne),
      f ∈ normOneTraceTestSpace F n ∧ φ ∈ normOneTraceTestSpace E n ∧
      D.base.normOneTrace H.baseNormOne f hf =
        (Module.finrank F E : ℂ) * D.upper.normOneTrace H.upperNormOne φ hφ

/-- II.(17.8) and III.(4.1)–(4.2) for prime cyclic base change. -/
def CyclicDiscreteTraceComparisonStatement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] (n : ℕ), 0 < n → (Module.finrank F E).Prime →
    ∀ (σ : E ≃ₐ[F] E), IsCyclicAlgebra σ (Module.finrank F E) →
    ∀ (H : CyclicTraceHaarData F E n) (t : ℝ), 0 ≤ t →
    ∀ D : CyclicDiscreteComparisonData H σ t, D.ComparedAtCenter

/-- II.(17.8) over a totally complex base, for the split archimedean comparison route. -/
def CyclicDiscreteTraceComparisonTCStatement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (n : ℕ), 0 < n → (Module.finrank F E).Prime →
    ∀ (σ : E ≃ₐ[F] E), IsCyclicAlgebra σ (Module.finrank F E) →
    ∀ (H : CyclicTraceHaarData F E n) (t : ℝ), 0 ≤ t →
    ∀ D : CyclicDiscreteComparisonData H σ t, D.ComparedAtCenter

/-- The split-centre reduction of (17.8) from (17.7), exposing the measure pushforward
and the two integrations used in the source. -/
def CyclicDiscreteTraceCenterReductionStatement : Prop :=
  CyclicNormOneDiscreteTraceComparisonStatement → CyclicSplitCenterMeasureStatement.{0, 0} →
    CyclicMatchedCentralTranslateStatement → CyclicCentralAverageTraceStatement →
    CyclicDiscreteTraceComparisonStatement

end Langlands.TraceFormula
