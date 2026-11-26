import Langlands.Automorphic.CuspidalAdmissible.Existence
import Langlands.Automorphic.CuspidalPresentationUniverse
import Langlands.Automorphic.CuspidalSlicePresentation
import Langlands.Automorphic.Unramified.CuspidalSpectralAttachmentExistenceStatement

/-! # Genuine cuspidal spectra in an independent factor universe: proof

An irreducible admissible finite slice of the supplied realization, Flath's
factorization of that slice with factors in the field universe, and the
small-realization transport of the irreducible admissible local factors give a
spectral presentation of the same realization with factors in the prescribed
universe. Its numerical spectrum is attached to the realization's class.
-/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global
open Langlands.Automorphic.CuspidalOperatorRealization

/-- Every actual cuspidal realization has a numerical spectrum attached through a
spectral presentation whose local factors lie in the independent universe `uV`. -/
theorem cuspidalSpectralAttachmentExistence :
    CuspidalSpectralAttachmentExistenceStatement.{uF, uV} := by
  intro F _ _ _ r T
  obtain ⟨A, hI, hA⟩ := cuspidalIrreducibleAdmissibleFiniteSliceExistence F r T
  obtain ⟨P, hP⟩ := T.exists_presentation_of_finiteSlice A hI hA
  obtain ⟨Q, -⟩ : ∃ Q : CuspidalSpectralPresentation.{uF, uV} T,
      ∀ v, (Q.localComponent v).IsIrreducible ∧ (Q.localComponent v).IsAdmissible :=
    P.exists_small hP
  exact ⟨Q.spectralSystem, (IsoClass.hasSpectralSystem_iff T Q.spectralSystem).mpr ⟨Q, rfl⟩⟩

end Langlands.Automorphic.Unramified
