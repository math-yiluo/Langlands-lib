import Langlands.Global.Factors.RelativeIsometryOperationReduction
import Langlands.ClassFieldTheory.Local.WeilReciprocityExistenceProof
import Langlands.ClassField.Global.LocalRelativeWeilMapExistenceProof
import Langlands.Automorphic.AssociatedCentralCharacterProof
import Langlands.Automorphic.CuspidalUnitaryContragredientExistenceProof
import Langlands.Automorphic.CuspidalContragredientPresentationExistenceProof
import Langlands.Automorphic.CuspidalContragredientLocalCompatibilityProof
import Langlands.Automorphic.Unramified.ContragredientAssociation
import Langlands.Automorphic.CuspidalDeterminantMultipleProof
import Langlands.Automorphic.HeckeDeterminantTwistAssociationProof
import Langlands.ClassField.Global.LocalRelativeWeilTransferProof
import Langlands.Global.Arithmetic.UnitaryLocalCharacterExtensionProof

/-! # Contragredient, twist and character compatibility of the relative generated isometry

Proof of `Langlands.Global.PoleComparison.RelativeIsometryOperationStatement`. The published
reduction `relativeIsometryOperationStatement_of_globalInputs` derives the target from eleven
global inputs; each of them is a published proved theorem, and this module supplies them. -/

noncomputable section

universe uF uW uP

namespace Langlands.Global.PoleComparison

/-- Every generated positive isometry `T` between the relative Weil image and the relative
automorphic image at a finite place is compatible with contragredients, with twists by
modulus-one characters and with rank-one characters. -/
theorem relativeIsometryOperation : RelativeIsometryOperationStatement.{uF, uW, uP} :=
  relativeIsometryOperationStatement_of_globalInputs
    Langlands.LocalClassField.geometricWeilReciprocityExistenceUniqueness
    Langlands.ClassField.Global.localRelativeWeilMapExistence
    Langlands.ClassField.Global.RelativeWeilGroup.associatedCentralCharacter
    Langlands.Automorphic.cuspidalUnitaryContragredientExistence
    Langlands.Automorphic.cuspidalContragredientPresentationExistence
    Langlands.Automorphic.cuspidalContragredientLocalCompatibility
    Langlands.ClassField.Global.RelativeWeilGroup.presentedContragredientAssociation
    Langlands.Automorphic.cuspidalDeterminantMultiple
    Langlands.ClassField.Global.RelativeWeilGroup.presentedDeterminantMultipleAssociation
    Langlands.ClassField.Global.RelativeWeilGroup.localTransferReciprocity
    Langlands.Global.unitaryLocalCharacterExtension

end Langlands.Global.PoleComparison
