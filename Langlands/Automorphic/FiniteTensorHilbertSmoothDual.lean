import Langlands.Automorphic.FiniteTensorHilbertSmoothComponents
import Langlands.Automorphic.PresentedLocalCategory

/-! # Smooth-dual representatives in actual completed automorphic slices -/

noncomputable section
open CategoryTheory
open scoped Classical TensorProduct
universe uF uV
set_option autoImplicit false
set_option maxHeartbeats 20000

namespace Langlands.SmoothDualClass

universe uR uG uA

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

/-- The full irreducible admissible subcategory reflects equality of smooth classes. -/
theorem ofRep_eq_iff_isoClass_eq
    (A B : Langlands.IrreducibleAdmissibleRep.{uR, uG, uA} (k := k) (G := G)) :
    ofRep A = ofRep B ↔
      Langlands.SmoothRep.isoClass A.obj = Langlands.SmoothRep.isoClass B.obj := by
  change Quotient.mk _ A = Quotient.mk _ B ↔ _
  rw [Quotient.eq, Langlands.SmoothRep.isoClass_eq_iff]
  constructor
  · rintro ⟨e⟩
    exact ⟨(Langlands.irreducibleAdmissibleProperty (k := k) (G := G)).ι.mapIso e⟩
  · rintro ⟨e⟩
    exact ⟨ObjectProperty.isoMk _ e⟩

end Langlands.SmoothDualClass

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorHilbertSmoothDualRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertSmoothDualContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertSmoothDualSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertSmoothDualFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance tensorHilbertSmoothDualFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertSmoothDualLocalSpaceGroup
    (v : FinitePlace F) (L : LocalRealization F n v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- An actual irreducible admissible representative inside the completed global action. -/
def sliceHilbertSmoothObject (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hI : (ρ v).IsIrreducible) (hA : IsAdmissible (ρ v)) :
    Langlands.IrreducibleAdmissibleRep.{0, uF, uF}
      (k := ℂ) (G := FiniteLocalGL F n v) :=
  ⟨P.sliceHilbertSmoothRepresentation b v y,
    P.sliceHilbertSmoothRange_isIrreducible b v y hy hA hI,
    P.sliceHilbertSmoothRange_isAdmissible b v y hy hA⟩

/-- The genuine smooth-dual class of that completed smooth-slice representative. -/
def sliceHilbertSmoothDualClass (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hI : (ρ v).IsIrreducible) (hA : IsAdmissible (ρ v)) :
    Langlands.SmoothDualClass.{0, uF, uF} (k := ℂ) (G := FiniteLocalGL F n v) :=
  Langlands.SmoothDualClass.ofRep (P.sliceHilbertSmoothObject b v y hy hI hA)

/-- The refined class is independent of supplied forms, presentations and nonzero tails. -/
theorem sliceHilbertSmoothDualClass_eq {S' : FiniteRealization F n}
    (Q : FiniteTensorPresentation F n ρ E e he S')
    (c : Langlands.InvariantPositiveForm S'.representation) (v : FinitePlace F)
    (y z : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hz : FiniteTensorRealization.TailNonzero F E e v z)
    (hI : (ρ v).IsIrreducible) (hA : IsAdmissible (ρ v)) :
    P.sliceHilbertSmoothDualClass b v y hy hI hA =
      Q.sliceHilbertSmoothDualClass c v z hz hI hA :=
  (Langlands.SmoothDualClass.ofRep_eq_iff_isoClass_eq _ _).mpr
    (P.sliceHilbertSmoothClass_eq b Q c v y z hy hz hA)

/-- The completed smooth representative and the existing embedded component have
the same refined class. -/
theorem sliceHilbertSmoothDualClass_eq_localComponent
    (hS : S.IsNonzero F n) (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hI : (ρ v).IsIrreducible) (hA : IsAdmissible (ρ v)) :
    P.sliceHilbertSmoothDualClass b v y hy hI hA =
      P.localComponentDualClass hS v hI hA :=
  (Langlands.SmoothDualClass.ofRep_eq_iff_isoClass_eq _ _).mpr
    ((P.sliceHilbertSmoothClass_eq_slice b v y hy hA).trans
      (P.localComponentClass_eq_slice hS v y hy).symm)

/-- Restrict the actual factor equivalence to any subgroup-fixed spaces. -/
def sliceHilbertSmoothFixedEquiv (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hA : IsAdmissible (ρ v)) (K : Subgroup (FiniteLocalGL F n v)) :
    Langlands.fixedVectors (ρ v) K ≃ₗ[ℂ]
      Langlands.fixedVectors (P.sliceHilbertSmoothRange b v y).toRepresentation K :=
  Langlands.fixedVectorsEquiv (P.factorHilbertSmoothEquiv b v y hy hA) K

/-- The refined class has a subgroup-fixed vector exactly when the given factor does. -/
theorem sliceHilbertSmoothDualClass_hasFixedVector_iff
    (v : FinitePlace F) (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hI : (ρ v).IsIrreducible) (hA : IsAdmissible (ρ v))
    (K : Subgroup (FiniteLocalGL F n v)) :
    Langlands.SmoothDualClass.HasFixedVector K
      (P.sliceHilbertSmoothDualClass b v y hy hI hA) ↔
        Langlands.fixedVectors (ρ v) K ≠ ⊥ :=
  (Langlands.fixedVectors_ne_bot_iff_of_equiv
    (P.factorHilbertSmoothEquiv b v y hy hA) K).symm

/-- Outside the exceptional set the actual smooth-dual class is integral-spherical. -/
theorem sliceHilbertSmoothDualClass_hasIntegralFixedVector
    (v : FinitePlace F) (hv : v ∉ E)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hI : (ρ v).IsIrreducible) (hA : IsAdmissible (ρ v)) :
    Langlands.SmoothDualClass.HasFixedVector (localIntegral F n v).toSubgroup
      (P.sliceHilbertSmoothDualClass b v y hy hI hA) := by
  apply (P.sliceHilbertSmoothDualClass_hasFixedVector_iff b v y hy hI hA _).mpr
  apply (Langlands.fixedVectors (ρ v) (localIntegral F n v).toSubgroup).ne_bot_iff.mpr
  refine ⟨e v, ?_, P.reference_nonzero v hv⟩
  intro g
  exact he v hv g g.property

end FiniteTensorPresentation
end Langlands.Automorphic
