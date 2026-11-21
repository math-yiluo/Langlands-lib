import Langlands.TraceFormula.CyclicDiscreteTraceDistribution
import Langlands.Global.AdelicWeilNormOneComparison

/-! # Arthur–Clozel (17.7) on the actual cyclic norm-one adelic groups -/

noncomputable section

open MeasureTheory
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.BaseChange
open AdelicGroupAutomorphism NormOneLeviInduction
open scoped CoordinateLevi.Presentation

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [FiniteDimensional F E] (n : ℕ)

/-- The actual Weil-restriction comparison, oriented from the Weil side over `F` to
matrix group-scheme points over `E`. -/
structure CyclicWeilAdelicTransport where
  toUpper : AdelicGroupPoints F (cyclicWeilGroup F E n) ≃ₜ*
    AdelicGroupPoints E (cyclicBaseGroup E n)
  matrixComparison (x : AdelicGroupPoints F (cyclicWeilGroup F E n)) :
    GeneralLinearGroupPoints.adelicHomeomorph E n (toUpper x) = cyclicWeilAdelicMap F E n x
  normOneComparison : (normOneSubgroup F (cyclicWeilGroup F E n)).map toUpper.toMonoidHom =
    normOneSubgroup E (cyclicBaseGroup E n)
  arithmeticComparison (σ : E ≃ₐ[F] E) (x : AdelicGroupPoints F (cyclicWeilGroup F E n)) :
    toUpper (adelicAut F (unitGaloisAut F E (cyclicBaseGroup F n) σ) x) =
      adelicFieldAutomorphism E n (σ : E ≃+* E) (toUpper x)

/-- The scalar subgroup acts by actual positive scalar ideles in logarithmic coordinates. -/
def positiveScalarPoint (a : ℝ) : AdelicGroupPoints F (cyclicBaseGroup F n) :=
  (GeneralLinearGroupPoints.adelicHomeomorph F n).symm
    (adelicPositiveScalar F n (PositiveRealTorus.expUnit a))

/-- A norm-one Haar measure disintegrates the given full Haar measure with the
specified positive split-centre Haar measure. -/
def IsNormOneHaarDecomposition (da : Measure ℝ)
    (ν : Measure (normOneSubgroup F (cyclicBaseGroup F n)))
    (full : Measure (AdelicGroupPoints F (cyclicBaseGroup F n))) : Prop :=
  ν.IsHaarMeasure ∧ MeasurePreserving
    (fun p : ℝ × normOneSubgroup F (cyclicBaseGroup F n) => positiveScalarPoint F n p.1 * p.2.val)
    (da.prod ν) full

/-- The Haar measures in the associated local tests and in both spectral sums. -/
structure CyclicTraceHaarData where
  transport : CyclicWeilAdelicTransport F E n
  localHaar : CyclicLocalHaarData F E n
  baseFull : Measure (AdelicGroupPoints F (cyclicBaseGroup F n))
  upperFull : Measure (AdelicGroupPoints F (cyclicWeilGroup F E n))
  localCompatible : localHaar.IsCompatible baseFull upperFull
  baseNormOne : Measure (normOneSubgroup F (cyclicBaseGroup F n))
  upperNormOne : Measure (normOneSubgroup E (cyclicBaseGroup E n))
  baseDecomposition : IsNormOneHaarDecomposition F n (cyclicBaseCenterMeasure F E n)
    baseNormOne baseFull
  upperDecomposition : IsNormOneHaarDecomposition E n (cyclicUpperCenterMeasure E n)
    upperNormOne (Measure.map transport.toUpper upperFull)

/-- The transport and norm-one Haar decompositions for the full measures given by
compatible local Haar measures. -/
def CyclicNormOneTraceHaarStatement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] (n : ℕ), 0 < n →
    ∀ (H : CyclicLocalHaarData F E n) (μF : Measure (AdelicGroupPoints F (cyclicBaseGroup F n)))
      (μE : Measure (AdelicGroupPoints F (cyclicWeilGroup F E n))), H.IsCompatible μF μE →
    ∃ A : CyclicTraceHaarData F E n,
      A.localHaar = H ∧ A.baseFull = μF ∧ A.upperFull = μE

variable {F E n}

/-- The ordinary and arithmetic spectral data giving the actual discrete distributions. -/
structure CyclicDiscreteComparisonData (H : CyclicTraceHaarData F E n) (σ : E ≃ₐ[F] E) (t : ℝ) where
  base : DiscreteTraceData F n t
  upper : DiscreteTraceData E n t
  baseSpectral : base.IsSpectral
  upperSpectral : upper.IsSpectral
  baseOrdinary : base.IsOrdinary
  upperArithmetic : upper.IsArithmetic (σ : E ≃+* E)
  baseDistribution : base.HasNormOneDistribution H.baseNormOne
  upperDistribution : upper.HasNormOneDistribution H.upperNormOne

/-- The equality of the norm-one discrete distributions for associated tests, in
base-then-upper order. This is II.(17.7) for prime cyclic base change. -/
def CyclicNormOneDiscreteTraceComparisonStatement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] (n : ℕ), 0 < n → (Module.finrank F E).Prime →
    ∀ (σ : E ≃ₐ[F] E), IsCyclicAlgebra σ (Module.finrank F E) →
    ∀ (H : CyclicTraceHaarData F E n) (t : ℝ), 0 ≤ t →
    ∀ (D : CyclicDiscreteComparisonData H σ t) (p : cyclicMatchedTests H.localHaar σ),
      let f : normOneSubgroup F (cyclicBaseGroup F n) → ℂ := fun x => p.val.1 x.val
      let φ : normOneSubgroup E (cyclicBaseGroup E n) → ℂ :=
        fun x => p.val.2 (H.transport.toUpper.symm x.val)
      ∃ (hf : Integrable f H.baseNormOne) (hφ : Integrable φ H.upperNormOne),
        f ∈ normOneTraceTestSpace F n ∧ φ ∈ normOneTraceTestSpace E n ∧
        D.base.normOneTrace H.baseNormOne f hf = D.upper.normOneTrace H.upperNormOne φ hφ

end Langlands.TraceFormula
