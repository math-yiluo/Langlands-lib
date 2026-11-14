import Langlands.Representation.GodementJacquet.SubquotientCoefficientInclusionStatement
import Langlands.AllField.Representation.GodementJacquet.Zeta
/-!
# Bi-smooth coefficient inclusion for actual subquotients

The general statement uses compact-open cofinality and smoothness of the
ambient representation. The p-adic specialization uses the canonical topology.
These are statements, with no coefficient-inclusion proof in this module.
-/

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

universe uG uF uV uW

namespace Padic
open Langlands.GodementJacquet.Padic hiding MatrixConverges SubquotientCoefficientInclusionStatement instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instTopologicalSpaceCarrier instValuativeRelCarrier jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding MatrixConverges SubquotientCoefficientInclusionStatement jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet

/-- The canonical p-adic general-linear specialization, with no extra
compact-open, admissibility, irreducibility, or target-smoothness premise. -/
def SubquotientCoefficientInclusionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    ∀ (n : ℕ)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
      (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
      IsSmooth σ →
      ∀ (A : Subrepresentation σ)
        (q : A.toRepresentation.IntertwiningMap τ),
        Function.Surjective q →
          biSmoothMatrixCoefficients τ ≤ biSmoothMatrixCoefficients σ

end Padic

end Langlands.AllField.GodementJacquet
