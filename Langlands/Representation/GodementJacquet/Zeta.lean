import Langlands.Representation.MatrixCoefficient.Definitions
import Langlands.Representation.Smooth.Contragredient.Definitions
import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.LocalField.Canonical

/-!
# Godement–Jacquet matrix integrals and JPSS Section 5.2 value modules

The test functions live on the full matrix space. The integral has exponent `s`;
the rational-value sets use `s + n/2` at actual rank `n + 1`. Convergence and
rational continuation are membership conditions, with no existence assertion.
-/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis Whittaker RankinSelberg
open scoped nonZeroDivisors

universe uF uG uV

section Coefficients

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A coefficient with both its functional and vector in the actual smooth parts. -/
def biSmoothCoefficient (σ : Representation ℂ G V)
    (ℓ : SmoothDual σ) (v : smoothVectors σ) : G → ℂ :=
  matrixCoefficient σ (smoothDualPairing σ ℓ) v.val

/-- The complex span of coefficients from smooth functionals and smooth vectors.
No irreducibility, admissibility, or smoothness of the whole representation is required. -/
def biSmoothMatrixCoefficients (σ : Representation ℂ G V) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ {f | ∃ (ℓ : SmoothDual σ) (v : smoothVectors σ),
    biSmoothCoefficient σ ℓ v = f}

end Coefficients

section MatrixIntegrals

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}

/-- Schwartz–Bruhat functions on all square matrices, including singular matrices. -/
abbrev MatrixTestFunction (n : ℕ) (F : Type uF) [TopologicalSpace F] :=
  SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F)

/-- The unshifted full-matrix integrand of JPSS Section 5.2, equations (2),(3). -/
def matrixIntegrand (abv : AbsoluteValue F ℝ) (Φ : MatrixTestFunction n F)
    (s : ℂ) (f : Langlands.GeneralLinear (n + 1) F → ℂ)
    (g : Langlands.GeneralLinear (n + 1) F) : ℂ :=
  Φ g.val * f g * determinantWeight abv g s

variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]

/-- Absolute convergence at `s` for the explicit Borel group measure. -/
def MatrixConverges (abv : AbsoluteValue F ℝ)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (Φ : MatrixTestFunction n F) (s : ℂ)
    (f : Langlands.GeneralLinear (n + 1) F → ℂ) : Prop :=
  Integrable (matrixIntegrand abv Φ s f) μ

/-- The scalar matrix integral with exponent `s`. This is the totalized Bochner
integral; convergence is expressed separately by `MatrixConverges`. -/
def matrixIntegral (abv : AbsoluteValue F ℝ)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (Φ : MatrixTestFunction n F) (s : ℂ)
    (f : Langlands.GeneralLinear (n + 1) F → ℂ) : ℂ :=
  ∫ g, matrixIntegrand abv Φ s f g ∂μ

/-- The JPSS shift `(d-1)/2` at actual rank `d = n+1`, as a complex number. -/
def jpssShift (n : ℕ) : ℂ := (n : ℂ) / 2

/-- Convergence on some right half-plane for the shifted matrix integral. -/
def ShiftedConvergesOnRight (abv : AbsoluteValue F ℝ)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (Φ : MatrixTestFunction n F)
    (f : Langlands.GeneralLinear (n + 1) F → ℂ) : Prop :=
  ∃ a : ℝ, ∀ s : ℂ, a < s.re → MatrixConverges abv μ Φ (s + jpssShift n) f

/-- A rational value of the shifted integral, with an actual convergence witness.
The continuation convention is `spectralPoint q s = q^(-s)`, with unshifted `s`
as the rational-function variable. No continuation is selected. -/
def HasShiftedRationalValue (q : ℕ) (abv : AbsoluteValue F ℝ)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (Φ : MatrixTestFunction n F) (f : Langlands.GeneralLinear (n + 1) F → ℂ)
    (R : RationalFunctions) : Prop :=
  ShiftedConvergesOnRight abv μ Φ f ∧
    HasRationalContinuation q (fun s => matrixIntegral abv μ Φ (s + jpssShift n) f) R

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Rational values from actual bi-smooth matrix coefficients, before Laurent span. -/
def matrixRationalValues (q : ℕ) (abv : AbsoluteValue F ℝ)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) :
    Set RationalFunctions :=
  {R | ∃ Φ : MatrixTestFunction n F, ∃ f : biSmoothMatrixCoefficients σ,
    HasShiftedRationalValue q abv μ Φ f.val R}

/-- Rational values from the coefficient-image model of the specified standard
Whittaker functional. This does not range over all equivariant functions. -/
def whittakerRationalValues (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : glFunctionals ψ n σ) : Set RationalFunctions :=
  {R | ∃ Φ : MatrixTestFunction n F, ∃ w : (glCoefficientModel ψ n σ ℓ).toSubmodule,
    HasShiftedRationalValue q abv μ Φ (glModelFunction ψ n σ ℓ w) R}

/-- The Laurent module called `I₂` in JPSS, before any common-denominator theorem. -/
def jpssI2 (q : ℕ) (abv : AbsoluteValue F ℝ)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) :
    Submodule LaurentCoefficients RationalFunctions :=
  zetaSpan (matrixRationalValues q abv μ σ)

/-- The Laurent module called `I₃` in JPSS for the specified coefficient model. -/
def jpssI3 (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : glFunctionals ψ n σ) : Submodule LaurentCoefficients RationalFunctions :=
  zetaSpan (whittakerRationalValues q ψ abv μ σ ℓ)

/-- Package `I₂` as a fractional ideal only with a proof for its actual value set. -/
def jpssI2FractionalIdeal (q : ℕ) (abv : AbsoluteValue F ℝ)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (h : HasCommonDenominator (matrixRationalValues q abv μ σ)) :
    FractionalIdeal LaurentCoefficients⁰ RationalFunctions :=
  fractionalZetaIdeal (matrixRationalValues q abv μ σ) h

/-- Package `I₃` as a fractional ideal only with a proof for its actual value set. -/
def jpssI3FractionalIdeal (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : glFunctionals ψ n σ)
    (h : HasCommonDenominator (whittakerRationalValues q ψ abv μ σ ℓ)) :
    FractionalIdeal LaurentCoefficients⁰ RationalFunctions :=
  fractionalZetaIdeal (whittakerRationalValues q ψ abv μ σ ℓ) h

end MatrixIntegrals

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ}

/-- The matrix integrand with the canonical residue-normalized absolute value. -/
def matrixIntegrand (Φ : MatrixTestFunction n F.Carrier) (s : ℂ)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) :
    Langlands.GeneralLinear (n + 1) F.Carrier → ℂ :=
  GodementJacquet.matrixIntegrand (normalizedAbsoluteValue F.canonicalTopologicalData) Φ s f

/-- Convergence for the shared Haar measure with integral general linear group
of mass one, on the canonical p-adic topology and its Borel space. -/
def MatrixConverges (Φ : MatrixTestFunction n F.Carrier) (s : ℂ)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) : Prop :=
  GodementJacquet.MatrixConverges (normalizedAbsoluteValue F.canonicalTopologicalData)
    (generalLinearHaar F.Carrier n) Φ s f

/-- The unshifted matrix integral with the shared normalized general-linear Haar measure. -/
def matrixIntegral (Φ : MatrixTestFunction n F.Carrier) (s : ℂ)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) : ℂ :=
  GodementJacquet.matrixIntegral (normalizedAbsoluteValue F.canonicalTopologicalData)
    (generalLinearHaar F.Carrier n) Φ s f

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Shifted matrix-coefficient values with canonical topology, normalized absolute
value, residue cardinality and the shared normalized Haar measure. -/
def matrixRationalValues
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V) :
    Set RationalFunctions :=
  GodementJacquet.matrixRationalValues F.canonicalTopologicalData.residueCardinality
    (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier n) σ

/-- Shifted values from the actual model of the specified standard Whittaker
functional, with the same canonical normalization as the matrix coefficients. -/
def whittakerRationalValues (ψ : UnitaryAdditiveCharacter F.Carrier)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ n σ) : Set RationalFunctions :=
  GodementJacquet.whittakerRationalValues F.canonicalTopologicalData.residueCardinality ψ
    (normalizedAbsoluteValue F.canonicalTopologicalData) (generalLinearHaar F.Carrier n) σ ℓ

/-- The canonical p-adic JPSS `I₂` Laurent module. -/
def jpssI2 (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V) :
    Submodule LaurentCoefficients RationalFunctions :=
  zetaSpan (matrixRationalValues F σ)

/-- The canonical p-adic JPSS `I₃` Laurent module for the specified model. -/
def jpssI3 (ψ : UnitaryAdditiveCharacter F.Carrier)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ n σ) : Submodule LaurentCoefficients RationalFunctions :=
  zetaSpan (whittakerRationalValues F ψ σ ℓ)

end Padic

end Langlands.GodementJacquet
