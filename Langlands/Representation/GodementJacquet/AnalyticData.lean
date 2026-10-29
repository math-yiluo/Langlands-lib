import Langlands.Representation.GodementJacquet.Zeta
import Langlands.HarmonicAnalysis.RectangularFourier
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement

/-!
# Actual matrix analytic assertions and transpose Fourier data

These predicates record common shifted convergence, actual rational
continuations, normalized generators and the transpose Fourier functional
equation. They assert no existence theorem, including for reducible carriers.
-/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg

universe uF uV

section TransformedCoefficients

variable {F : Type uF} [Field F] {n : ℕ}

/-- Explicit inverse-transpose transformation of a function. No equivalence
with a smooth contragredient coefficient space is assumed. -/
def coefficientIota (f : Langlands.GeneralLinear (n + 1) F → ℂ) :
    Langlands.GeneralLinear (n + 1) F → ℂ :=
  fun g => f (GeneralLinear.inverseTranspose (n + 1) F g)

end TransformedCoefficients

section MatrixAnalytics

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Shifted rational values of inverse-transpose transforms of the original
actual bi-smooth coefficients, over all full-matrix Schwartz tests. -/
def iotaMatrixRationalValues (q : ℕ) (abv : AbsoluteValue F ℝ)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) :
    Set RationalFunctions :=
  {R | ∃ Φ : MatrixTestFunction n F, ∃ f : biSmoothMatrixCoefficients σ,
    HasShiftedRationalValue q abv μ Φ (coefficientIota f.val) R}

/-- One right half-plane of actual shifted convergence for every full-matrix
test and every actual bi-smooth coefficient of the specified representation. -/
def MatrixConvergesOnRight (abv : AbsoluteValue F ℝ)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) : Prop :=
  ∃ a : ℝ, ∀ Φ : MatrixTestFunction n F, ∀ f : biSmoothMatrixCoefficients σ,
    ∀ s : ℂ, a < s.re → MatrixConverges abv μ Φ (s + jpssShift n) f.val

/-- The analogous common half-plane for the inverse-transpose functions
obtained from the same original coefficient family. -/
def IotaMatrixConvergesOnRight (abv : AbsoluteValue F ℝ)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) : Prop :=
  ∃ a : ℝ, ∀ Φ : MatrixTestFunction n F, ∀ f : biSmoothMatrixCoefficients σ,
    ∀ s : ℂ, a < s.re →
      MatrixConverges abv μ Φ (s + jpssShift n) (coefficientIota f.val)

/-- `P(0)=1` and reciprocal-polynomial generation for exactly the published
matrix rational-value family. No default polynomial is selected. -/
def IsMatrixNormalizedGenerator (q : ℕ) (abv : AbsoluteValue F ℝ)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (P : Polynomial ℂ) : Prop :=
  IsNormalizedGenerator (matrixRationalValues q abv μ σ) P

/-- Reciprocal-polynomial generation for the actual transformed value family. -/
def IsIotaMatrixNormalizedGenerator (q : ℕ) (abv : AbsoluteValue F ℝ)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (P : Polynomial ℂ) : Prop :=
  IsNormalizedGenerator (iotaMatrixRationalValues q abv μ σ) P

/-- Common shifted convergence, rational continuation for every actual pair,
and the proposed normalized generator of the published matrix value family. -/
def MatrixAnalyticAssertions (q : ℕ) (abv : AbsoluteValue F ℝ)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (P : Polynomial ℂ) : Prop :=
  MatrixConvergesOnRight abv μ σ ∧
    (∀ Φ : MatrixTestFunction n F, ∀ f : biSmoothMatrixCoefficients σ,
      ∃ R : RationalFunctions, HasShiftedRationalValue q abv μ Φ f.val R) ∧
    IsMatrixNormalizedGenerator q abv μ σ P

/-- The corresponding actual analytic assertions for the inverse-transpose
coefficient functions; these are not identified with a contragredient by definition. -/
def IotaMatrixAnalyticAssertions (q : ℕ) (abv : AbsoluteValue F ℝ)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (P : Polynomial ℂ) : Prop :=
  IotaMatrixConvergesOnRight abv μ σ ∧
    (∀ Φ : MatrixTestFunction n F, ∀ f : biSmoothMatrixCoefficients σ,
      ∃ R : RationalFunctions,
        HasShiftedRationalValue q abv μ Φ (coefficientIota f.val) R) ∧
    IsIotaMatrixNormalizedGenerator q abv μ σ P

end MatrixAnalytics

section FourierData

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n : ℕ}

/-- An actual full-matrix Fourier pair in the plus transpose convention.
The entry pairing is `Tr(y * transpose x)`. Integrability is retained at every
matrix, and the integral uses exactly the supplied scalar product measure. -/
def MatrixFourierPair (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (Φ ΦHat : MatrixTestFunction n F) : Prop :=
  ∀ x : Matrix (Fin (n + 1)) (Fin (n + 1)) F,
    Integrable (fun y => Φ y * ψ.complex (rectangularPairing y x))
      (rectangularMeasure ν (n + 1) (n + 1)) ∧
    ΦHat x = rectangularFourierIntegral ψ ν Φ x

variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Proposed normalized matrix functional-equation data. Both analytic
assertions and a Schwartz Fourier witness for each test are required.
The fixed polynomials, unit `c` and integer `m` work for all original
coefficients and all their continuations, with both denominator guards.
The matrix convention uses central scalar `1` and sign exponent `0`. -/
def NormalizedMatrixFunctionalEquationData (q : ℕ)
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (P PDual : Polynomial ℂ) (c : ℂˣ) (m : ℤ) : Prop :=
  MatrixAnalyticAssertions q abv μ σ P ∧
    IotaMatrixAnalyticAssertions q abv μ σ PDual ∧
    ∀ Φ : MatrixTestFunction n F, ∃ ΦHat : MatrixTestFunction n F,
      MatrixFourierPair ψ ν Φ ΦHat ∧
      ∀ f : biSmoothMatrixCoefficients σ, ∀ R RDual : RationalFunctions,
        HasShiftedRationalValue q abv μ Φ f.val R →
        HasShiftedRationalValue q abv μ ΦHat (coefficientIota f.val) RDual →
        NormalizedFunctionalEquation q P PDual 1 c 0 m R RDual

end FourierData

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : MeasurableSpace F.Carrier := borel _
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Transformed values with the canonical p-adic normalizations of `Zeta`. -/
def iotaMatrixRationalValues
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V) :
    Set RationalFunctions :=
  GodementJacquet.iotaMatrixRationalValues F.canonicalTopologicalData.residueCardinality
    (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier n) σ

/-- Common shifted convergence with canonical topology and normalized group Haar measure. -/
def MatrixConvergesOnRight
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V) : Prop :=
  GodementJacquet.MatrixConvergesOnRight (normalizedAbsoluteValue F.canonicalTopologicalData)
    (generalLinearHaar F.Carrier n) σ

/-- Common transformed shifted convergence with the same canonical group measure. -/
def IotaMatrixConvergesOnRight
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V) : Prop :=
  GodementJacquet.IotaMatrixConvergesOnRight
    (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier n) σ

/-- A proposed normalized generator for the canonical published matrix values. -/
def IsMatrixNormalizedGenerator
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (P : Polynomial ℂ) : Prop :=
  GodementJacquet.IsMatrixNormalizedGenerator F.canonicalTopologicalData.residueCardinality
    (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier n) σ P

/-- A proposed normalized generator for the canonical transformed values. -/
def IsIotaMatrixNormalizedGenerator
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (P : Polynomial ℂ) : Prop :=
  GodementJacquet.IsIotaMatrixNormalizedGenerator
    F.canonicalTopologicalData.residueCardinality
    (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier n) σ P

/-- Actual matrix analytic assertions with all canonical p-adic normalizations. -/
def MatrixAnalyticAssertions
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (P : Polynomial ℂ) : Prop :=
  GodementJacquet.MatrixAnalyticAssertions F.canonicalTopologicalData.residueCardinality
    (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier n) σ P

/-- Transformed analytic assertions with the same canonical p-adic normalizations. -/
def IotaMatrixAnalyticAssertions
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (P : Polynomial ℂ) : Prop :=
  GodementJacquet.IotaMatrixAnalyticAssertions F.canonicalTopologicalData.residueCardinality
    (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier n) σ P

/-- The actual plus transpose Fourier relation with canonical Borel structures.
The scalar additive measure is supplied, with no normalization change. -/
def MatrixFourierPair (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier) (Φ ΦHat : MatrixTestFunction n F.Carrier) : Prop :=
  GodementJacquet.MatrixFourierPair ψ ν Φ ΦHat

/-- Canonical p-adic functional-equation data retaining the supplied scalar
Fourier measure. Self-duality is a premise for later existence theorems. -/
def NormalizedMatrixFunctionalEquationData (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (P PDual : Polynomial ℂ) (c : ℂˣ) (m : ℤ) : Prop :=
  GodementJacquet.NormalizedMatrixFunctionalEquationData
    F.canonicalTopologicalData.residueCardinality ψ ν
    (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier n)
    σ P PDual c m

end Padic

end Langlands.GodementJacquet
