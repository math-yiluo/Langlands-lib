import Langlands.Representation.GodementJacquet.Zeta
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement
/-!
# Godement–Jacquet matrix integrals and JPSS Section 5.2 value modules

The test functions live on the full matrix space. The integral has exponent `s`;
the rational-value sets use `s + n/2` at actual rank `n + 1`. Convergence and
rational continuation are membership conditions, with no existence assertion.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg
open scoped nonZeroDivisors

universe uF uG uV

section Coefficients


end Coefficients

section MatrixIntegrals




end MatrixIntegrals

namespace Padic
open Langlands.GodementJacquet.Padic hiding MatrixConverges instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instTopologicalSpaceCarrier instValuativeRelCarrier jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding MatrixConverges jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) :=
  borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {n : ℕ}

/-- The matrix integrand with the canonical residue-normalized absolute value. -/
def matrixIntegrand (Φ : MatrixTestFunction n F) (s : ℂ)
    (f : Langlands.GeneralLinear (n + 1) F → ℂ) :
    Langlands.GeneralLinear (n + 1) F → ℂ :=
  GodementJacquet.matrixIntegrand (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) Φ s f

/-- Convergence for the shared Haar measure with integral general linear group
of mass one, on the canonical p-adic topology and its Borel space. -/
def MatrixConverges (Φ : MatrixTestFunction n F) (s : ℂ)
    (f : Langlands.GeneralLinear (n + 1) F → ℂ) : Prop :=
  GodementJacquet.MatrixConverges (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
    (generalLinearHaar F n) Φ s f

/-- The unshifted matrix integral with the shared normalized general-linear Haar measure. -/
def matrixIntegral (Φ : MatrixTestFunction n F) (s : ℂ)
    (f : Langlands.GeneralLinear (n + 1) F → ℂ) : ℂ :=
  GodementJacquet.matrixIntegral (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
    (generalLinearHaar F n) Φ s f

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Shifted matrix-coefficient values with canonical topology, normalized absolute
value, residue cardinality and the shared normalized Haar measure. -/
def matrixRationalValues
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) :
    Set RationalFunctions :=
  GodementJacquet.matrixRationalValues (⟨⟩ : LocalFieldData F).residueCardinality
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F n) σ

/-- Shifted values from the actual model of the specified standard Whittaker
functional, with the same canonical normalization as the matrix coefficients. -/
def whittakerRationalValues (ψ : UnitaryAdditiveCharacter F)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : glFunctionals ψ n σ) : Set RationalFunctions :=
  GodementJacquet.whittakerRationalValues (⟨⟩ : LocalFieldData F).residueCardinality ψ
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F n) σ ℓ

/-- The canonical p-adic JPSS `I₂` Laurent module. -/
def jpssI2 (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) :
    Submodule LaurentCoefficients RationalFunctions :=
  zetaSpan (matrixRationalValues F σ)

/-- The canonical p-adic JPSS `I₃` Laurent module for the specified model. -/
def jpssI3 (ψ : UnitaryAdditiveCharacter F)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : glFunctionals ψ n σ) : Submodule LaurentCoefficients RationalFunctions :=
  zetaSpan (whittakerRationalValues F ψ σ ℓ)

end Padic

end Langlands.AllField.GodementJacquet
