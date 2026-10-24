import Langlands.Automorphic.PresentedLocalComponent
import Langlands.Representation.Category.ClassInvariants
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof
import Langlands.Representation.Classification.SupercuspidalContragredientAux

/-! # Irreducible admissible classes of actual presented local components -/

noncomputable section
open CategoryTheory
universe uF uV

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance categoryRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance categoryContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance categorySmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance categoryFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance categoryLocalSpaceAddCommGroup {v : FinitePlace F}
    (T : LocalRealization F n v) : AddCommGroup T.Space := Submodule.addCommGroup _

namespace LocalRealization

variable {v : FinitePlace F} (S : LocalRealization F n v)

/-- Irreducibility of the actual local action, including nonzeroness. -/
abbrev IsIrreducible : Prop := S.representation.IsIrreducible

/-- Admissibility for the existing completed-local topology. -/
abbrev IsAdmissible : Prop := Langlands.IsAdmissible S.representation

/-- Bundle the actual form subspace with explicit irreducibility and admissibility. -/
def irreducibleAdmissible (hI : S.IsIrreducible) (hA : S.IsAdmissible) :
    Langlands.IrreducibleAdmissibleRep.{0, uF, uF}
      (k := ℂ) (G := FiniteLocalGL F n v) :=
  ⟨S.smoothRepresentation, hI, hA⟩

/-- The class of the actual embedded irreducible admissible representation. -/
def dualClass (hI : S.IsIrreducible) (hA : S.IsAdmissible) :
    Langlands.SmoothDualClass.{0, uF, uF} (k := ℂ) (G := FiniteLocalGL F n v) :=
  Langlands.SmoothDualClass.ofRep (S.irreducibleAdmissible hI hA)

theorem dualClass_eq_iff (T : LocalRealization F n v)
    (hI : S.IsIrreducible) (hA : S.IsAdmissible)
    (hI' : T.IsIrreducible) (hA' : T.IsAdmissible) :
    S.dualClass hI hA = T.dualClass hI' hA' ↔
      Nonempty (S.representation.Equiv T.representation) := by
  change Quotient.mk _ (S.irreducibleAdmissible hI hA) =
    Quotient.mk _ (T.irreducibleAdmissible hI' hA') ↔ _
  rw [Quotient.eq]
  constructor
  · rintro ⟨e⟩
    exact ⟨Langlands.SmoothRep.equivOfIso
      ((Langlands.irreducibleAdmissibleProperty (k := ℂ)
        (G := FiniteLocalGL F n v)).ι.mapIso e)⟩
  · rintro ⟨e⟩
    exact ⟨ObjectProperty.isoMk _ (Langlands.SmoothRep.mkIso e)⟩

/-- The refined classes agree exactly when the underlying smooth classes agree. -/
theorem dualClass_eq_iff_isoClass_eq (T : LocalRealization F n v)
    (hI : S.IsIrreducible) (hA : S.IsAdmissible)
    (hI' : T.IsIrreducible) (hA' : T.IsAdmissible) :
    S.dualClass hI hA = T.dualClass hI' hA' ↔ S.isoClass = T.isoClass := by
  rw [S.dualClass_eq_iff T hI hA hI' hA', S.isoClass_eq_iff T]

theorem dualClass_hasFixedVector_iff (hI : S.IsIrreducible) (hA : S.IsAdmissible)
    (K : Subgroup (FiniteLocalGL F n v)) :
    Langlands.SmoothDualClass.HasFixedVector K (S.dualClass hI hA) ↔
      Langlands.fixedVectors S.representation K ≠ ⊥ := Iff.rfl

end LocalRealization

namespace FiniteTensorPresentation

variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n}
variable (P : FiniteTensorPresentation F n ρ E e he S)

theorem localComponent_isIrreducible_iff (hS : S.IsNonzero F n) (v : FinitePlace F) :
    (P.localComponent hS v).IsIrreducible ↔ (ρ v).IsIrreducible :=
  (Langlands.isIrreducible_iff_of_equiv (P.localComponentEquiv hS v)).symm

theorem localComponent_isAdmissible_iff (hS : S.IsNonzero F n) (v : FinitePlace F) :
    (P.localComponent hS v).IsAdmissible ↔ Langlands.IsAdmissible (ρ v) :=
  (Langlands.isAdmissible_iff_of_equiv (P.localComponentEquiv hS v)).symm

/-- The equivalence restricts to every subgroup-fixed space. -/
def localComponentFixedEquiv (hS : S.IsNonzero F n) (v : FinitePlace F)
    (K : Subgroup (FiniteLocalGL F n v)) :
    Langlands.fixedVectors (ρ v) K ≃ₗ[ℂ]
      Langlands.fixedVectors (P.localComponent hS v).representation K :=
  Langlands.fixedVectorsEquiv (P.localComponentEquiv hS v) K

/-- Irreducibility and admissibility remain explicit properties of the factor. -/
def localComponentObject (hS : S.IsNonzero F n) (v : FinitePlace F)
    (hI : (ρ v).IsIrreducible) (hA : Langlands.IsAdmissible (ρ v)) :
    Langlands.IrreducibleAdmissibleRep.{0, uF, uF}
      (k := ℂ) (G := FiniteLocalGL F n v) :=
  (P.localComponent hS v).irreducibleAdmissible
    ((P.localComponent_isIrreducible_iff hS v).mpr hI)
    ((P.localComponent_isAdmissible_iff hS v).mpr hA)

/-- The local factor's refined class has an actual form-space representative. -/
def localComponentDualClass (hS : S.IsNonzero F n) (v : FinitePlace F)
    (hI : (ρ v).IsIrreducible) (hA : Langlands.IsAdmissible (ρ v)) :
    Langlands.SmoothDualClass.{0, uF, uF} (k := ℂ) (G := FiniteLocalGL F n v) :=
  Langlands.SmoothDualClass.ofRep (P.localComponentObject hS v hI hA)

/-- Changing a presentation of fixed tensor data preserves the refined class. -/
theorem localComponentDualClass_eq {S' : FiniteRealization F n}
    (Q : FiniteTensorPresentation F n ρ E e he S')
    (hS : S.IsNonzero F n) (hS' : S'.IsNonzero F n) (v : FinitePlace F)
    (hI : (ρ v).IsIrreducible) (hA : Langlands.IsAdmissible (ρ v)) :
    P.localComponentDualClass hS v hI hA =
      Q.localComponentDualClass hS' v hI hA :=
  ((P.localComponent hS v).dualClass_eq_iff_isoClass_eq
    (Q.localComponent hS' v) _ _ _ _).mpr
      (P.localComponentClass_eq Q hS hS' v)

/-- Nonzero fixed vectors of the class are exactly those of the specified factor. -/
theorem localComponentDualClass_hasFixedVector_iff
    (hS : S.IsNonzero F n) (v : FinitePlace F)
    (hI : (ρ v).IsIrreducible) (hA : Langlands.IsAdmissible (ρ v))
    (K : Subgroup (FiniteLocalGL F n v)) :
    Langlands.SmoothDualClass.HasFixedVector K
      (P.localComponentDualClass hS v hI hA) ↔
        Langlands.fixedVectors (ρ v) K ≠ ⊥ :=
  (Langlands.fixedVectors_ne_bot_iff_of_equiv
    (P.localComponentEquiv hS v) K).symm

/-- Outside the exceptional set, this actual smooth-dual class is integral-spherical. -/
theorem localComponentDualClass_hasIntegralFixedVector
    (hS : S.IsNonzero F n) (v : FinitePlace F) (hv : v ∉ E)
    (hI : (ρ v).IsIrreducible) (hA : Langlands.IsAdmissible (ρ v)) :
    Langlands.SmoothDualClass.HasFixedVector (localIntegral F n v).toSubgroup
      (P.localComponentDualClass hS v hI hA) := by
  apply (P.localComponentDualClass_hasFixedVector_iff hS v hI hA _).mpr
  apply (Langlands.fixedVectors (ρ v) (localIntegral F n v).toSubgroup).ne_bot_iff.mpr
  refine ⟨e v, ?_, P.reference_nonzero v hv⟩
  intro g
  exact he v hv g g.property

end FiniteTensorPresentation
end Langlands.Automorphic
