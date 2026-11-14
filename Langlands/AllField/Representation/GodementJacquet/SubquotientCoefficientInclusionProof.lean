import Langlands.Representation.GodementJacquet.SubquotientCoefficientInclusionProof
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Representation.GodementJacquet.SubquotientCoefficientInclusionStatement
/-! # Bi-smooth coefficients of actual subquotients -/

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

universe uG uF uV uW

namespace Padic
open Langlands.GodementJacquet.Padic hiding MatrixConverges SubquotientCoefficientInclusionStatement instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instTopologicalSpaceCarrier instValuativeRelCarrier jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues subquotientCoefficientInclusion whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding MatrixConverges SubquotientCoefficientInclusionStatement jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues subquotientCoefficientInclusion whittakerRationalValues
open Langlands.AllField.GodementJacquet

/-- The coefficient inclusion for every canonical p-adic general linear group,
including rank one. -/
theorem subquotientCoefficientInclusion :
    SubquotientCoefficientInclusionStatement.{uF, uV, uW} := by
  intro F _ _ _ _
  intro n V _ _ W _ _ σ τ hσ A q hq
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (n + 1)
  have hcof : ∀ K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
      ∃ L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
        IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F)) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hL, hLK⟩ :=
      (⟨⟩ : LocalFieldData F).generalLinearCompactOpen (n + 1)
        (K : Set _) (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L, hL, hLK⟩
  exact GodementJacquet.subquotientCoefficientInclusion
    (Langlands.GeneralLinear (n + 1) F) hcof V W σ τ hσ A q hq

end Padic

end Langlands.AllField.GodementJacquet
