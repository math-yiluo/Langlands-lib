import Langlands.Correspondence.HenniartPadicArtinTransport
import Langlands.Correspondence.HenniartRefinedStrata
import Langlands.Correspondence.HenniartWeilConductorIntegralityProof

/-! # Integrality of the Artin conductor of a local Weil representation -/

namespace Langlands.Henniart

open Correspondence

universe uK uW

/-- Every irreducible Weil class over a p-adic field has a natural Artin conductor. -/
theorem weilArtinConductorExistence : WeilArtinConductorExistenceStatement.{uK, uW} := by
  intro p _ K k σ
  obtain ⟨A, hA⟩ := Quotient.exists_rep σ.val
  have hClass : FiniteRepresentation.classOf A.val = weilClassForget K σ :=
    congrArg (FiniteRepresentation.forgetPropertyClass _) hA
  obtain ⟨P, hP, a, -, ha, -⟩ := (weilConductorIntegrality p K A.val).2 A.property.1
  exact ⟨a, (Numerical.hasArtinConductor_iff_exists_padicPresentation K σ a).mpr
    ⟨A.val, P, hP, hClass, ha⟩⟩

end Langlands.Henniart
