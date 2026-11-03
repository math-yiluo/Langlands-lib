import Langlands.Automorphic.FiniteTensorHilbertSmoothComponents
import Langlands.Automorphic.PresentedUnramifiedData

/-! # Canonical p-adic objects of actual smooth Hilbert tensor slices -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV
set_option autoImplicit false
set_option maxHeartbeats 20000

namespace Langlands.TensorPadicAux

universe uK uG uW

variable {k : Type uK} [Field k] {G : Type uG} [Group G]
variable {W : Type uW} [AddCommGroup W] [Module k W]

/-- Equal group topologies preserve the actual carrier and action when bundling. -/
def objectOfTopologyEq (t t' : TopologicalSpace G) (ht : t = t')
    (τ : Representation k G W)
    (hs : @IsSmooth k G W _ _ _ _ t τ) (hI : τ.IsIrreducible)
    (hA : @IsAdmissible k G W _ _ _ _ t τ) :
    @IrreducibleAdmissibleRep.{uK, uG, uW} k _ G _ t' := by
  letI := t'
  refine ⟨Langlands.SmoothRep.of τ ?_, hI, ?_⟩
  · rw [← ht]
    exact hs
  · change @IsAdmissible k G W _ _ _ _ t' τ
    rw [← ht]
    exact hA

end Langlands.TensorPadicAux

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F]

local instance tensorHilbertPadicRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertPadicContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertPadicSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertPadicFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance tensorHilbertPadicFiniteSpaceGroup {n : ℕ} (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertPadicLocalSpaceGroup {n : ℕ}
    (v : FinitePlace F) (L : LocalRealization F n v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {r : ℕ} {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v, ρ v g (e v) = e v}
variable {S : FiniteRealization F (r + 1)}
variable (P : FiniteTensorPresentation F (r + 1) ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The actual intrinsic smooth Hilbert slice in the canonical correspondence category. -/
def sliceHilbertPadicObject (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hI : (ρ v).IsIrreducible) (hA : IsAdmissible (ρ v)) :
    Correspondence.AutomorphicObject.{uF, uF} (CompletionPadic.padicField v) r.succPNat :=
  Langlands.TensorPadicAux.objectOfTopologyEq _ _
    (localGL_topology_eq F v (r + 1))
    (P.sliceHilbertSmoothRange b v y).toRepresentation
    (P.sliceHilbertSmoothRange_isSmooth b v y)
    (P.sliceHilbertSmoothRange_isIrreducible b v y hy hA hI)
    (P.sliceHilbertSmoothRange_isAdmissible b v y hy hA)

/-- Its genuine class retains the representative inside the supplied global completion. -/
def sliceHilbertPadicClass (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hI : (ρ v).IsIrreducible) (hA : IsAdmissible (ρ v)) :
    Correspondence.AutomorphicClass.{uF, uF} (CompletionPadic.padicField v) r.succPNat :=
  Correspondence.automorphicClassOf _ (P.sliceHilbertPadicObject b v y hy hI hA)

/-- Supplied forms, presentations and nonzero tails of fixed tensor data give the same class. -/
theorem sliceHilbertPadicClass_eq {S' : FiniteRealization F (r + 1)}
    (Q : FiniteTensorPresentation F (r + 1) ρ E e he S')
    (c : Langlands.InvariantPositiveForm S'.representation) (v : FinitePlace F)
    (y z : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hz : FiniteTensorRealization.TailNonzero F E e v z)
    (hI : (ρ v).IsIrreducible) (hA : IsAdmissible (ρ v)) :
    P.sliceHilbertPadicClass b v y hy hI hA =
      Q.sliceHilbertPadicClass c v z hz hI hA :=
  (Correspondence.automorphicClassOf_eq_iff _ _ _).mpr
    ⟨P.sliceHilbertSmoothChangeEquiv b Q c v y z hy hz hA⟩

/-- The canonical class is the class of the existing actual form-space component. -/
theorem sliceHilbertPadicClass_eq_localComponent
    (hS : S.IsNonzero F (r + 1)) (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hI : (ρ v).IsIrreducible) (hA : IsAdmissible (ρ v)) :
    P.sliceHilbertPadicClass b v y hy hI hA = P.localPadicClass hS v hI hA :=
  (Correspondence.automorphicClassOf_eq_iff _ _ _).mpr
    ⟨(P.factorHilbertSmoothEquiv b v y hy hA).symm.trans (P.localComponentEquiv hS v)⟩

/-- Sphericality tests exactly nonzero integral fixedness of the original factor. -/
theorem sliceHilbertPadicClass_isSpherical_iff (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hI : (ρ v).IsIrreducible) (hA : IsAdmissible (ρ v)) :
    Correspondence.IsSphericalClass (CompletionPadic.padicField v)
      (P.sliceHilbertPadicClass b v y hy hI hA) ↔
        Langlands.fixedVectors (ρ v) (localIntegral F (r + 1) v).toSubgroup ≠ ⊥ := by
  rw [localIntegral_eq_sphericalSubgroup F v r]
  have hfixed := Langlands.fixedVectors_ne_bot_iff_of_equiv
    (P.factorHilbertSmoothEquiv b v y hy hA)
    (Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r)
  constructor
  · rintro ⟨A, hAeq, hAfix⟩
    obtain ⟨f⟩ := (Correspondence.automorphicClassOf_eq_iff _ A
      (P.sliceHilbertPadicObject b v y hy hI hA)).mp hAeq
    exact hfixed.mpr ((Langlands.fixedVectors_ne_bot_iff_of_equiv f _).mp hAfix)
  · intro h
    exact ⟨P.sliceHilbertPadicObject b v y hy hI hA, rfl, hfixed.mp h⟩

/-- The actual reference vector supplies sphericality outside the exceptional set. -/
theorem sliceHilbertPadicClass_isSpherical (v : FinitePlace F) (hv : v ∉ E)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hI : (ρ v).IsIrreducible) (hA : IsAdmissible (ρ v)) :
    Correspondence.IsSphericalClass (CompletionPadic.padicField v)
      (P.sliceHilbertPadicClass b v y hy hI hA) := by
  apply (P.sliceHilbertPadicClass_isSpherical_iff b v y hy hI hA).mpr
  apply (Langlands.fixedVectors (ρ v) (localIntegral F (r + 1) v).toSubgroup).ne_bot_iff.mpr
  refine ⟨e v, ?_, P.reference_nonzero v hv⟩
  intro g
  exact he v hv g g.property

/-- The full normalized Hecke scalar equations agree with those in the form-space component. -/
theorem sliceHilbertPadicObject_hasSpectrum_iff
    (hS : S.IsNonzero F (r + 1)) (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hI : (ρ v).IsIrreducible) (hA : IsAdmissible (ρ v))
    (s : Langlands.Unramified.Eigenvalues (r + 1)) :
    Langlands.Unramified.HasSphericalHeckeSpectrum (CompletionPadic.padicField v)
      (P.sliceHilbertPadicObject b v y hy hI hA) s ↔
        (P.localComponent hS v).HasSphericalHeckeSpectrum s := by
  rw [← Langlands.Unramified.hasSphericalHeckeSpectrumClass_classOf]
  change Langlands.Unramified.HasSphericalHeckeSpectrumClass _
    (P.sliceHilbertPadicClass b v y hy hI hA) s ↔ _
  rw [P.sliceHilbertPadicClass_eq_localComponent b hS v y hy hI hA]
  exact (P.localComponent hS v).hasSphericalHeckeSpectrumClass_iff _ _ s

namespace UnramifiedData

variable {P} {hS : S.IsNonzero F (r + 1)} {T : Finset (FinitePlace F)}
variable (D : P.UnramifiedData hS T)

/-- Supplied actual unramified data give the same whole-fixed-space spectrum in the completion. -/
theorem hasSpectrum_hilbertSmooth (v : FinitePlace F) (hv : v ∉ T)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :
    Langlands.Unramified.HasSphericalHeckeSpectrum (CompletionPadic.padicField v)
      (P.sliceHilbertPadicObject b v y hy (D.irreducible v hv) (D.admissible v hv))
      (D.eigenvalues v hv) :=
  (P.sliceHilbertPadicObject_hasSpectrum_iff b hS v y hy _ _ _).mpr (D.hasSpectrum v hv)

end UnramifiedData
end FiniteTensorPresentation
end Langlands.Automorphic
