import Langlands.Automorphic.Unramified.ContragredientAssociation
import Langlands.Automorphic.CuspidalDualPresentationExistenceProof

/-! # Contragredient association for actual cuspidal realizations and classes: proof -/

noncomputable section
universe u uV uP uQ
set_option autoImplicit false

namespace Langlands.ClassField.Global.RelativeWeilGroup

/-- The presented and class forms of contragredient association, at four independent
universe levels. -/
theorem associatedContragredient : AssociatedContragredientStatement.{u, uV, uP, uQ} :=
  ⟨presentedContragredientAssociation,
    classContragredientAssociation_of_dualPresentationExistence
      Automorphic.cuspidalDualPresentationExistence⟩

end Langlands.ClassField.Global.RelativeWeilGroup
