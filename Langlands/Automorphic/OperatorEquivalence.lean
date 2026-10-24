import Langlands.Automorphic.OperatorRealization

/-! # Full-operator equivalences of actual automorphic realizations -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T : OperatorRealization F n)

local instance : AddCommGroup S.Space := Submodule.addCommGroup _
local instance : AddCommGroup T.Space := Submodule.addCommGroup _

/-- The whole restricted concrete action retains its complex algebra structure. -/
def operatorAction : automorphicOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ S.Space where
  toFun := S.representation
  map_one' := S.representation.map_one
  map_mul' := S.representation.map_mul
  map_zero' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_add' a b := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    rfl
  commutes' c := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    rfl

@[simp]
theorem operatorAction_finite (d : FiniteAdelicGL F n) :
    S.operatorAction (finiteOperator F n d) = S.finiteRepresentation d := rfl

@[simp]
theorem operatorAction_compact (k : standardInfiniteCompact F n) :
    S.operatorAction (compactOperator F n k) = S.compactRepresentation k := rfl

@[simp]
theorem operatorAction_differential (a : ArchimedeanGL.EnvelopingAlgebra F n) :
    S.operatorAction (differentialOperator F n a) = S.envelopingAction a := rfl

/-- A linear map commutes with the full algebra exactly when it commutes with
each of the three actual operator families. -/
theorem intertwines_iff_generators (L : S.Space →ₗ[ℂ] T.Space) :
    (∀ a f, L (S.representation a f) = T.representation a (L f)) ↔
      (∀ d f, L (S.finiteRepresentation d f) = T.finiteRepresentation d (L f)) ∧
      (∀ k f, L (S.compactRepresentation k f) = T.compactRepresentation k (L f)) ∧
      (∀ a f, L (S.envelopingAction a f) = T.envelopingAction a (L f)) := by
  constructor
  · intro h
    exact ⟨fun d => h (finiteOperator F n d),
      fun k => h (compactOperator F n k), fun a => h (differentialOperator F n a)⟩
  · rintro ⟨hd, hk, hu⟩ a
    refine Algebra.adjoin_induction
      (p := fun a ha => ∀ f,
        L (S.operatorAction ⟨a, ha⟩ f) = T.operatorAction ⟨a, ha⟩ (L f))
      ?_ ?_ ?_ ?_ a.property
    · rintro a ((⟨d, rfl⟩ | ⟨k, rfl⟩) | ⟨v, rfl⟩)
      · exact hd d
      · exact hk k
      · exact hu v
    · intro c f
      change L (S.operatorAction (algebraMap ℂ _ c) f) =
        T.operatorAction (algebraMap ℂ _ c) (L f)
      change L (c • f) = c • L f
      exact L.map_smul c f
    · intro a b ha hb hLa hLb f
      change L (S.operatorAction (⟨a, ha⟩ + ⟨b, hb⟩) f) =
        T.operatorAction (⟨a, ha⟩ + ⟨b, hb⟩) (L f)
      simp only [map_add, LinearMap.add_apply, hLa, hLb]
    · intro a b ha hb hLa hLb f
      change L (S.operatorAction (⟨a, ha⟩ * ⟨b, hb⟩) f) =
        T.operatorAction (⟨a, ha⟩ * ⟨b, hb⟩) (L f)
      simp only [map_mul, Module.End.mul_apply, hLa, hLb]

/-- Maps respect the whole actual operator algebra. -/
abbrev Intertwiner := S.representation.IntertwiningMap T.representation

/-- Equivalences respect finite, compact and differential actions together. -/
abbrev Equivalence := S.representation.Equiv T.representation

namespace Intertwiner

variable {S T}

theorem finite (L : S.Intertwiner T) (d : FiniteAdelicGL F n) (f : S.Space) :
    L (S.finiteRepresentation d f) = T.finiteRepresentation d (L f) :=
  Representation.IntertwiningMap.isIntertwining _ _ L (finiteOperator F n d) f

theorem compact (L : S.Intertwiner T) (k : standardInfiniteCompact F n) (f : S.Space) :
    L (S.compactRepresentation k f) = T.compactRepresentation k (L f) :=
  Representation.IntertwiningMap.isIntertwining _ _ L (compactOperator F n k) f

theorem differential (L : S.Intertwiner T)
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : S.Space) :
    L (S.envelopingAction a f) = T.envelopingAction a (L f) :=
  Representation.IntertwiningMap.isIntertwining _ _ L (differentialOperator F n a) f

/-- Construct a full intertwiner by checking its concrete generators. -/
def ofGenerators (L : S.Space →ₗ[ℂ] T.Space)
    (hd : ∀ d f, L (S.finiteRepresentation d f) = T.finiteRepresentation d (L f))
    (hk : ∀ k f, L (S.compactRepresentation k f) = T.compactRepresentation k (L f))
    (hu : ∀ a f, L (S.envelopingAction a f) = T.envelopingAction a (L f)) :
    S.Intertwiner T where
  toLinearMap := L
  isIntertwining' a := LinearMap.ext ((S.intertwines_iff_generators T L).mpr ⟨hd, hk, hu⟩ a)

/-- Forget the extra operators while retaining the same linear map. -/
def finiteRestriction (L : S.Intertwiner T) :
    S.finiteRepresentation.IntertwiningMap T.finiteRepresentation where
  toLinearMap := L.toLinearMap
  isIntertwining' d := L.isIntertwining' (finiteOperator F n d)

end Intertwiner

namespace Equivalence

variable {S T}

/-- The same linear equivalence intertwines the restricted finite actions. -/
def finiteRestriction (e : S.Equivalence T) :
    S.finiteRepresentation.Equiv T.finiteRepresentation :=
  Representation.Equiv.mk e.toLinearEquiv
    (fun d => e.toIntertwiningMap.isIntertwining' (finiteOperator F n d))

/-- Transport the equivalence to the actual finite form images. -/
def finiteImage (e : S.Equivalence T) :
    S.toFiniteRealization.representation.Equiv T.toFiniteRealization.representation :=
  S.finiteEquiv.symm.trans ((finiteRestriction e).trans T.finiteEquiv)

@[simp]
theorem finiteImage_apply (e : S.Equivalence T) (f : S.Space) :
    finiteImage e (S.finiteEquiv f) = T.finiteEquiv (e f) := by
  change T.finiteEquiv (e (S.finiteEquiv.symm (S.finiteEquiv f))) = _
  rw [Representation.Equiv.symm_apply_apply]

/-- Construct a full equivalence by checking its concrete generators. -/
def ofGenerators (e : S.Space ≃ₗ[ℂ] T.Space)
    (hd : ∀ d f, e (S.finiteRepresentation d f) = T.finiteRepresentation d (e f))
    (hk : ∀ k f, e (S.compactRepresentation k f) = T.compactRepresentation k (e f))
    (hu : ∀ a f, e (S.envelopingAction a f) = T.envelopingAction a (e f)) :
    S.Equivalence T :=
  Representation.Equiv.mk e (fun a =>
    LinearMap.ext ((S.intertwines_iff_generators T e.toLinearMap).mpr ⟨hd, hk, hu⟩ a))

end Equivalence

variable (F n)

/-- Equivalence of actual realized spaces, with every operator retained. -/
def equivalenceSetoid : Setoid (OperatorRealization F n) where
  r S T := Nonempty (S.Equivalence T)
  iseqv :=
    ⟨fun S => ⟨Representation.Equiv.refl S.representation⟩,
      fun ⟨e⟩ => ⟨e.symm⟩,
      fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- Full-operator classes of realized subspaces; this is not a subquotient category. -/
def IsoClass := Quotient (equivalenceSetoid F n)

variable {F n}

def isoClass (S : OperatorRealization F n) : IsoClass F n :=
  Quotient.mk (equivalenceSetoid F n) S

theorem isoClass_eq_iff :
    S.isoClass = T.isoClass ↔ Nonempty (S.Equivalence T) :=
  Quotient.eq

/-- A full-operator class has a well-defined finite smooth representation class. -/
def IsoClass.finiteClass (c : IsoClass F n) :
    Langlands.SmoothRep.IsoClass.{0, u, u} ℂ (FiniteAdelicGL F n) :=
  Quotient.lift (s := equivalenceSetoid F n)
    (fun S : OperatorRealization F n => S.toFiniteRealization.isoClass)
    (fun S T ⟨e⟩ => (S.toFiniteRealization.isoClass_eq_iff T.toFiniteRealization).mpr
      ⟨Equivalence.finiteImage e⟩) c

@[simp]
theorem finiteClass_isoClass :
    S.isoClass.finiteClass = S.toFiniteRealization.isoClass := rfl

end OperatorRealization
end Langlands.Automorphic
