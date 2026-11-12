import Langlands.Automorphic.CuspidalAllLocalIrreduciblePresentation
import Langlands.Automorphic.CuspidalSlicePresentation
import Langlands.Automorphic.CuspidalAdmissible.Existence

/-! # Cuspidal presentations irreducible and admissible at every finite place -/

noncomputable section
universe u uQ
set_option autoImplicit false

namespace Langlands.Automorphic

/-- **Reduction.** The intermediate proposition (an irreducible admissible actual finite
slice) implies the principal one: Flath factorization of that slice gives a spectral
presentation, with factors in the form-space universe, whose actual local components are
irreducible and admissible at every finite place. The supplied presentation is unused. -/
theorem cuspidalAllLocalIrreduciblePresentationExistence_of_finiteSlice
    (h : CuspidalIrreducibleAdmissibleFiniteSliceExistenceStatement.{u}) :
    CuspidalAllLocalIrreduciblePresentationExistenceStatement.{u, uQ} := by
  intro F _ _ _ r S _P
  obtain ⟨A, hI, hA⟩ := h F r S
  exact S.exists_presentation_of_finiteSlice A hI hA

/-- Every cuspidal operator realization with a supplied spectral presentation also has a
spectral presentation, with factors in the form-space universe, whose actual local components
are irreducible and admissible at every finite place. -/
theorem cuspidalAllLocalIrreduciblePresentationExistence :
    CuspidalAllLocalIrreduciblePresentationExistenceStatement.{u, uQ} :=
  cuspidalAllLocalIrreduciblePresentationExistence_of_finiteSlice
    cuspidalIrreducibleAdmissibleFiniteSliceExistence

end Langlands.Automorphic
