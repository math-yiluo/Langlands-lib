import Langlands.Automorphic.CuspidalAdmissible.Existence
import Langlands.Automorphic.CuspidalDualPresentationExistenceStatement
import Langlands.Automorphic.CuspidalPresentationUniverse
import Langlands.Automorphic.CuspidalSlicePresentation

/-! # Spectral presentations of supplied cuspidal contragredients: proof -/

noncomputable section
universe uF uP uQ
set_option autoImplicit false

namespace Langlands.Automorphic

/-- Every supplied full-operator contragredient `T'` of a presented cuspidal realization has a
spectral presentation in any factor universe: an irreducible admissible finite slice of `T'`,
Flath's theorem on that slice, and the small-realization transport. -/
theorem cuspidalDualPresentationExistence :
    CuspidalDualPresentationExistenceStatement.{uF, uP, uQ} := by
  intro F _ _ _ r _T T' _hdual _P
  obtain ⟨A, hI, hA⟩ := cuspidalIrreducibleAdmissibleFiniteSliceExistence F r T'
  obtain ⟨P, hP⟩ := T'.exists_presentation_of_finiteSlice A hI hA
  obtain ⟨Q, _⟩ := P.exists_small hP
  exact ⟨Q⟩

end Langlands.Automorphic
