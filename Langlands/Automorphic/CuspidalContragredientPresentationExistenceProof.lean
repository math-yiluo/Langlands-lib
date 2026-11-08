import Langlands.Automorphic.CuspidalContragredientStatement
import Langlands.Automorphic.CuspidalContragredientSlice
import Langlands.Automorphic.CuspidalSlicePresentation

/-! # Spectral presentations of supplied unitary cuspidal duals: proof -/

noncomputable section
universe uF uP uQ
set_option autoImplicit false

namespace Langlands.Automorphic

/-- Every supplied actual full-operator contragredient of a cuspidal realization with unitary
central character has an actual spectral presentation in every factor universe, with
irreducible admissible local components at every finite place. -/
theorem cuspidalContragredientPresentationExistence :
    CuspidalContragredientPresentationExistenceStatement.{uF, uP, uQ} := by
  intro F _ _ _ r T T' hT hdual _P
  obtain ⟨A, hI, hA⟩ :=
    T.exists_irreducibleAdmissible_finiteSlice_of_contragredient T' hT hdual
  obtain ⟨P, hP⟩ := T'.exists_presentation_of_finiteSlice A hI hA
  exact P.exists_small hP

end Langlands.Automorphic
