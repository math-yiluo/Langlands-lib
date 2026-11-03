import Langlands.Automorphic.FiniteTensorHilbertSmoothEquiv
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof
import Langlands.Representation.Filtration.LengthTwoMatching

/-! # Smooth representation objects of actual completed tensor slices -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV
set_option autoImplicit false
set_option maxHeartbeats 20000

namespace Langlands.TensorSmoothRangeAux

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A : Type uA} [AddCommGroup A] [Module ℂ A]
variable {τ : Representation ℂ G A}

/-- An invariant subspace of the ambient smooth vectors is itself smooth. -/
theorem isSmooth_of_le_smoothSubrepresentation (R : Subrepresentation τ)
    (hR : R ≤ Langlands.smoothSubrepresentation τ) :
    IsSmooth R.toRepresentation := by
  intro z
  obtain ⟨K, hK⟩ := hR z.property
  refine ⟨K, ?_⟩
  intro k
  apply Subtype.ext
  exact hK k

end Langlands.TensorSmoothRangeAux

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorHilbertSmoothComponentsRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertSmoothComponentsContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertSmoothComponentsSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorHilbertSmoothComponentsFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance tensorHilbertSmoothComponentsFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertSmoothComponentsLocalSpaceGroup
    (v : FinitePlace F) (L : LocalRealization F n v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- Intrinsic smoothness uses neither admissibility nor a nonzero tail. -/
theorem sliceHilbertSmoothRange_isSmooth (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    IsSmooth (P.sliceHilbertSmoothRange b v y).toRepresentation :=
  TensorSmoothRangeAux.isSmooth_of_le_smoothSubrepresentation _ inf_le_right

/-- The actual smooth slice as an object, before passing to any class. -/
def sliceHilbertSmoothRepresentation (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    Langlands.SmoothRep.{0, uF, uF} ℂ (FiniteLocalGL F n v) :=
  Langlands.SmoothRep.of (P.sliceHilbertSmoothRange b v y).toRepresentation
    (P.sliceHilbertSmoothRange_isSmooth b v y)

/-- The class retains an actual representative in the global completion's universe. -/
def sliceHilbertSmoothClass (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    Langlands.SmoothRep.IsoClass.{0, uF, uF} ℂ (FiniteLocalGL F n v) :=
  Langlands.SmoothRep.isoClass (P.sliceHilbertSmoothRepresentation b v y)

/-- Admissibility is proved by the genuine original-factor equivalence. -/
theorem sliceHilbertSmoothRange_isAdmissible (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hρ : IsAdmissible (ρ v)) :
    IsAdmissible (P.sliceHilbertSmoothRange b v y).toRepresentation :=
  Langlands.isAdmissible_of_equiv (P.factorHilbertSmoothEquiv b v y hy hρ) hρ

/-- Algebraic irreducibility of the local factor passes to the smooth slice. -/
theorem sliceHilbertSmoothRange_isIrreducible (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hρ : IsAdmissible (ρ v)) (hI : (ρ v).IsIrreducible) :
    (P.sliceHilbertSmoothRange b v y).toRepresentation.IsIrreducible :=
  Langlands.LengthTwo.isIrreducible_of_equiv
    (P.factorHilbertSmoothEquiv b v y hy hρ) hI

/-- Compare the existing algebraic form slice with the intrinsic smooth Hilbert slice. -/
def sliceToHilbertSmoothEquiv (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hρ : IsAdmissible (ρ v)) :=
  (P.sliceEquiv v y hy).symm.trans (P.factorHilbertSmoothEquiv b v y hy hρ)

/-- The Hilbert smooth representative has the existing algebraic slice's class. -/
theorem sliceHilbertSmoothClass_eq_slice (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hρ : IsAdmissible (ρ v)) :
    P.sliceHilbertSmoothClass b v y = (P.slice v y).isoClass :=
  (Langlands.SmoothRep.isoClass_eq_iff _ _).mpr
    ⟨Langlands.SmoothRep.mkIso (P.sliceToHilbertSmoothEquiv b v y hy hρ).symm⟩

/-- Two supplied forms, presentations and nonzero tails of the same tensor data
give equivalent actual smooth slices. -/
def sliceHilbertSmoothChangeEquiv {S' : FiniteRealization F n}
    (Q : FiniteTensorPresentation F n ρ E e he S')
    (c : Langlands.InvariantPositiveForm S'.representation) (v : FinitePlace F)
    (y z : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hz : FiniteTensorRealization.TailNonzero F E e v z)
    (hρ : IsAdmissible (ρ v)) :=
  (P.factorHilbertSmoothEquiv b v y hy hρ).symm.trans
    (Q.factorHilbertSmoothEquiv c v z hz hρ)

/-- The class is independent of those choices within the fixed tensor data. -/
theorem sliceHilbertSmoothClass_eq {S' : FiniteRealization F n}
    (Q : FiniteTensorPresentation F n ρ E e he S')
    (c : Langlands.InvariantPositiveForm S'.representation) (v : FinitePlace F)
    (y z : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hz : FiniteTensorRealization.TailNonzero F E e v z)
    (hρ : IsAdmissible (ρ v)) :
    P.sliceHilbertSmoothClass b v y = Q.sliceHilbertSmoothClass c v z :=
  (Langlands.SmoothRep.isoClass_eq_iff _ _).mpr
    ⟨Langlands.SmoothRep.mkIso (P.sliceHilbertSmoothChangeEquiv b Q c v y z hy hz hρ)⟩

end FiniteTensorPresentation
end Langlands.Automorphic
