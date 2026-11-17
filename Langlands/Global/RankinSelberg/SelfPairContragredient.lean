import Langlands.Automorphic.CuspidalUnitaryContragredientExistenceProof
import Langlands.Automorphic.CuspidalDualPresentationExistenceProof
import Langlands.Automorphic.ContragredientSphericalSpectrum
import Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingStatement

/-! # The conjugate realization as a presented cuspidal contragredient -/

noncomputable section
universe u uQ
open NumberField
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Global.RankinSelbergGlobal.SelfPair

open Automorphic CuspidalPairBoundaryNonvanishing
open Langlands.ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ}

/-- The actual pointwise-conjugate realization is a full-operator contragredient
of a cuspidal realization with unitary central character. -/
theorem conjugate_isContragredientOf (T : CuspidalOperatorRealization F r)
    (hT : HasUnitaryCentralCharacter T) :
    T.conjugate.realization.IsContragredientOf T.realization := by
  obtain ⟨b⟩ := CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter T hT
  have hA := CuspidalAdmissible.isJointlyAdmissible_of_siegelFiniteness
    PrimitiveAdelicHeight.siegelSetGLFiniteness T hT
  exact OperatorRealization.isContragredientOf_of_unitaryForm b hA
    T.conjugateEquiv T.conjugateEquiv_finite T.conjugateEquiv_compact
    T.conjugateEquiv_lieAction

/-- Every supplied presentation of the original realization gives existence of
a presentation of the actual conjugate in the same factor universe. -/
theorem exists_conjugatePresentation (T : CuspidalOperatorRealization F r)
    (hT : HasUnitaryCentralCharacter T) (P : CuspidalSpectralPresentation.{u, uQ} T) :
    Nonempty (CuspidalSpectralPresentation.{u, uQ} T.conjugate) :=
  cuspidalDualPresentationExistence F r T T.conjugate (conjugate_isContragredientOf T hT) P

/-- Conjugate and supplied contragredient presentations have equal spherical
spectra at every place where all three presentations are unramified. -/
theorem conjugate_eigenvalues_eq {T Td : CuspidalOperatorRealization F r}
    (hT : HasUnitaryCentralCharacter T)
    (hTd : Td.realization.IsContragredientOf T.realization)
    (P : CuspidalSpectralPresentation.{u, uQ} T)
    (Pc : CuspidalSpectralPresentation.{u, uQ} T.conjugate)
    (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
    (v : FinitePlace F) (hv : v ∉ P.exceptional)
    (hvc : v ∉ Pc.exceptional) (hvd : v ∉ Pd.exceptional) :
    Pc.spectralSystem.eigenvalues v hvc = Pd.spectralSystem.eigenvalues v hvd := by
  rw [CuspidalOperatorRealization.eigenvalues_eq_map_inv_of_isContragredientOf
    T T.conjugate P Pc (conjugate_isContragredientOf T hT) v hv hvc,
    CuspidalOperatorRealization.eigenvalues_eq_map_inv_of_isContragredientOf
      T Td P Pd hTd v hv hvd]

/-- The pair Euler factors agree after replacing the supplied contragredient
presentation by any presentation of the actual conjugate realization. -/
theorem partialEulerFactor_conjugate_eq {T Td : CuspidalOperatorRealization F r}
    (hT : HasUnitaryCentralCharacter T)
    (hTd : Td.realization.IsContragredientOf T.realization)
    (P : CuspidalSpectralPresentation.{u, uQ} T)
    (Pc : CuspidalSpectralPresentation.{u, uQ} T.conjugate)
    (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
    {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (hPc : Pc.exceptional ⊆ S) (hPd : Pd.exceptional ⊆ S)
    (v : {v : FinitePlace F // v ∉ S}) (s : ℂ) :
    partialEulerFactor P Pc hP hPc v s = partialEulerFactor P Pd hP hPd v s := by
  unfold partialEulerFactor
  rw [conjugate_eigenvalues_eq hT hTd P Pc Pd v.1
    (fun h => v.2 (hP h)) (fun h => v.2 (hPc h)) (fun h => v.2 (hPd h))]

/-- Internal presented-conjugate existence statement. -/
def PresentedConjugateContragredientStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ) (T : CuspidalOperatorRealization K r),
    HasUnitaryCentralCharacter T →
    CuspidalSpectralPresentation.{u, uQ} T →
    T.conjugate.realization.IsContragredientOf T.realization ∧
      Nonempty (CuspidalSpectralPresentation.{u, uQ} T.conjugate)

/-- Proof from the unitary form, joint admissibility and dual presentation
existence in the Library. -/
theorem presentedConjugateContragredient :
    PresentedConjugateContragredientStatement.{u, uQ} :=
  fun _ _ _ _ _ T hT P =>
    ⟨conjugate_isContragredientOf T hT, exists_conjugatePresentation T hT P⟩

end Langlands.Global.RankinSelbergGlobal.SelfPair
