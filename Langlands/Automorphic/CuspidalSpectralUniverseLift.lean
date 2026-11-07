import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Representation.Category.UniverseLift

/-! # Raising the factor universe of a cuspidal spectral presentation -/

noncomputable section
universe uX uF uV

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL

variable {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance liftRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance liftContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance liftSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance liftFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance liftLocalSpaceAddCommGroup {n : ℕ} {v : FinitePlace F}
    (L : LocalRealization F n v) : AddCommGroup L.Space := Submodule.addCommGroup _

namespace CuspidalSpectralPresentation

variable {r : ℕ} {S : CuspidalOperatorRealization F r}
variable (P : CuspidalSpectralPresentation.{uF, uV} S)

/-- Raise the carriers of the supplied local factors. -/
def universeLiftFactor (v : FinitePlace F) :
    Langlands.SmoothRep.{0, uF, max uV uX} ℂ (FiniteLocalGL F (r + 1) v) :=
  (P.localFactor v).universeLift.{uX}

/-- The reference vector is carried along by `ULift.up`. -/
def universeLiftReference (v : FinitePlace F) : P.universeLiftFactor.{uX} v :=
  ULift.up (P.reference v)

theorem universeLiftReference_fixed (v : FinitePlace F) (hv : v ∉ P.tensorExceptional)
    (g : FiniteLocalGL F (r + 1) v) (hg : g ∈ localIntegral F (r + 1) v) :
    (P.universeLiftFactor.{uX} v).representation g (P.universeLiftReference.{uX} v) =
      P.universeLiftReference.{uX} v :=
  congrArg ULift.up (P.reference_fixed v hv g hg)

/-- Component equivalences induce an equivariant equivalence of the actual
restricted tensor products. -/
def universeLiftTensorEquiv :
    (tensorRepresentation F (r + 1) (fun v => (P.localFactor v).representation)
      P.tensorExceptional P.reference P.reference_fixed).Equiv
    (tensorRepresentation F (r + 1) (fun v => (P.universeLiftFactor.{uX} v).representation)
      P.tensorExceptional P.universeLiftReference.{uX} P.universeLiftReference_fixed.{uX}) :=
  Representation.Equiv.mk
    (Langlands.RestrictedTensor.congr P.tensorExceptional P.tensorExceptional
      P.reference P.universeLiftReference.{uX}
      (fun v => ((P.localFactor v).universeLiftEquiv.{uX}).toLinearEquiv)
      (Filter.Eventually.of_forall fun _ => rfl))
    (fun g => (tensorIntertwiner F (r + 1)
      (fun v => (P.localFactor v).representation)
      (fun v => (P.universeLiftFactor.{uX} v).representation)
      P.tensorExceptional P.tensorExceptional P.reference P.universeLiftReference.{uX}
      P.reference_fixed P.universeLiftReference_fixed.{uX}
      (fun v => ((P.localFactor v).universeLiftEquiv.{uX}).toIntertwiningMap)
      (Filter.Eventually.of_forall fun _ => rfl)).isIntertwining' g)

/-- The lifted tensor product presents the original actual finite slice. -/
def universeLiftPresentation :
    FiniteTensorPresentation F (r + 1)
      (fun v => (P.universeLiftFactor.{uX} v).representation)
      P.tensorExceptional P.universeLiftReference.{uX} P.universeLiftReference_fixed.{uX}
      P.finiteSlice.subspace where
  reference_nonzero v hv h :=
    P.presentation.reference_nonzero v hv (congrArg ULift.down h)
  equiv := P.universeLiftTensorEquiv.symm.trans P.presentation.equiv

/-- The chosen embedded components may differ, but their actual actions are
equivalent through their respective factor identifications. -/
def universeLiftLocalEquiv (v : FinitePlace F) :
    ((P.universeLiftPresentation.{uX}).localComponent P.finiteSlice.nonzero v).representation.Equiv
      (P.localComponent v).representation :=
  ((P.universeLiftPresentation.{uX}).localComponentEquiv P.finiteSlice.nonzero v).symm.trans
    (((P.localFactor v).universeLiftEquiv.{uX}).symm.trans
      (P.presentation.localComponentEquiv P.finiteSlice.nonzero v))

/-- Transfer the supplied spectra through equality of genuine p-adic classes. -/
def universeLiftUnramified :
    (P.universeLiftPresentation.{uX}).UnramifiedData P.finiteSlice.nonzero P.exceptional where
  exceptional_subset := P.unramified.exceptional_subset
  irreducible v hv :=
    (Langlands.isIrreducible_universeLift_iff (P.localFactor v).representation).mpr
      (P.unramified.irreducible v hv)
  admissible v hv :=
    (Langlands.isAdmissible_universeLift_iff (P.localFactor v).representation).mpr
      (P.unramified.admissible v hv)
  eigenvalues := P.unramified.eigenvalues
  hasSpectrum v hv := by
    let Q := P.universeLiftPresentation.{uX}
    have hI : ((P.universeLiftFactor.{uX} v).representation).IsIrreducible :=
      (Langlands.isIrreducible_universeLift_iff (P.localFactor v).representation).mpr
        (P.unramified.irreducible v hv)
    have hA : Langlands.IsAdmissible (P.universeLiftFactor.{uX} v).representation :=
      (Langlands.isAdmissible_universeLift_iff (P.localFactor v).representation).mpr
        (P.unramified.admissible v hv)
    have hIQ := (Q.localComponent_isIrreducible_iff P.finiteSlice.nonzero v).mpr hI
    have hAQ := (Q.localComponent_isAdmissible_iff P.finiteSlice.nonzero v).mpr hA
    have hIP := (P.presentation.localComponent_isIrreducible_iff P.finiteSlice.nonzero v).mpr
      (P.unramified.irreducible v hv)
    have hAP := (P.presentation.localComponent_isAdmissible_iff P.finiteSlice.nonzero v).mpr
      (P.unramified.admissible v hv)
    have hc := ((Q.localComponent P.finiteSlice.nonzero v).padicClass_eq_iff
      (P.localComponent v) hIQ hAQ hIP hAP).mpr ⟨P.universeLiftLocalEquiv.{uX} v⟩
    apply ((Q.localComponent P.finiteSlice.nonzero v).hasSphericalHeckeSpectrumClass_iff
      hIQ hAQ _).mp
    rw [hc]
    exact ((P.localComponent v).hasSphericalHeckeSpectrumClass_iff hIP hAP _).mpr
      (P.unramified.hasSpectrum v hv)

/-- Raise only the local factor universe, keeping the realization, finite slice,
exceptional sets and numerical spectra. -/
def universeLift : CuspidalSpectralPresentation.{uF, max uV uX} S where
  finiteSlice := P.finiteSlice
  localFactor := P.universeLiftFactor.{uX}
  tensorExceptional := P.tensorExceptional
  reference := P.universeLiftReference.{uX}
  reference_fixed := P.universeLiftReference_fixed.{uX}
  presentation := P.universeLiftPresentation.{uX}
  exceptional := P.exceptional
  unramified := P.universeLiftUnramified.{uX}

@[simp] theorem universeLift_spectralSystem :
    (P.universeLift.{uX}).spectralSystem = P.spectralSystem := rfl

@[simp] theorem universeLift_localComponent (v : FinitePlace F) :
    (P.universeLift.{uX}).localComponent v =
      (P.universeLiftPresentation.{uX}).localComponent P.finiteSlice.nonzero v := rfl

theorem universeLift_localComponent_isoClass (v : FinitePlace F) :
    ((P.universeLift.{uX}).localComponent v).isoClass = (P.localComponent v).isoClass := by
  rw [universeLift_localComponent]
  exact (((P.universeLiftPresentation.{uX}).localComponent P.finiteSlice.nonzero v).isoClass_eq_iff
    (P.localComponent v)).mpr ⟨P.universeLiftLocalEquiv.{uX} v⟩

theorem universeLift_localComponent_isIrreducible_iff (v : FinitePlace F) :
    ((P.universeLift.{uX}).localComponent v).IsIrreducible ↔
      (P.localComponent v).IsIrreducible := by
  rw [universeLift_localComponent]
  exact Langlands.isIrreducible_iff_of_equiv (P.universeLiftLocalEquiv.{uX} v)

theorem universeLift_localComponent_isAdmissible_iff (v : FinitePlace F) :
    ((P.universeLift.{uX}).localComponent v).IsAdmissible ↔
      (P.localComponent v).IsAdmissible := by
  rw [universeLift_localComponent]
  exact Langlands.isAdmissible_iff_of_equiv (P.universeLiftLocalEquiv.{uX} v)

end CuspidalSpectralPresentation
end Langlands.Automorphic
