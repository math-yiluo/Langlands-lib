import Langlands.Automorphic.FullOperatorRealization

/-! # Actual quotients of whole-operator automorphic realizations -/

noncomputable section
universe uF uV
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

local instance subquotientRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance subquotientContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance subquotientSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance subquotientFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance subquotientStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance subquotientRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-- Concrete numerator inside actual forms, followed by an actual invariant denominator. -/
structure OperatorSubquotient where
  upper : OperatorRealization F n
  lower : Subrepresentation upper.representation

namespace OperatorSubquotient

variable {F n} (Q : OperatorSubquotient F n)

/-- The actual module quotient of the specified numerator by its denominator. -/
abbrev Space := Q.upper.Space ⧸ Q.lower.toSubmodule

/-- Every concrete operator acts by Mathlib's induced action on the module quotient. -/
def representation : Representation ℂ (automorphicOperatorAlgebra F n) Q.Space :=
  Q.upper.representation.quotient Q.lower.toSubmodule Q.lower.apply_mem_toSubmodule

/-- The canonical whole-operator equivariant quotient map. -/
def projection : Q.upper.representation.IntertwiningMap Q.representation where
  toLinearMap := Q.lower.toSubmodule.mkQ
  isIntertwining' _ := by ext; rfl

theorem projection_surjective : Function.Surjective Q.projection :=
  Submodule.mkQ_surjective _

@[simp] theorem projection_eq_zero_iff (f : Q.upper.Space) :
    Q.projection f = 0 ↔ f ∈ Q.lower :=
  Submodule.Quotient.mk_eq_zero _

@[simp] theorem projection_ker : Q.projection.ker = Q.lower := by
  apply Subrepresentation.toSubmodule_injective
  exact Submodule.ker_mkQ _

@[simp] theorem representation_projection (a : automorphicOperatorAlgebra F n)
    (f : Q.upper.Space) :
    Q.representation a (Q.projection f) =
      Q.projection (Q.upper.representation a f) := rfl

set_option maxHeartbeats 800000 in
/-- Additive and complex scalar laws descend from the genuine numerator algebra action. -/
def operatorAction : automorphicOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ Q.Space where
  toFun := Q.representation
  map_one' := Q.representation.map_one
  map_mul' a b := Q.representation.map_mul a b
  map_zero' := by
    change Q.representation (0 : automorphicOperatorAlgebra F n) =
      (0 : Module.End ℂ Q.Space)
    apply LinearMap.ext
    intro f
    refine Submodule.Quotient.induction_on Q.lower.toSubmodule f ?_
    intro v
    change Q.projection (Q.upper.operatorAction 0 v) = 0
    have hz : Q.upper.operatorAction 0 = (0 : Module.End ℂ Q.upper.Space) :=
      Q.upper.operatorAction.map_zero'
    exact (congrArg (fun m : Module.End ℂ Q.upper.Space => Q.projection (m v)) hz).trans
      Q.projection.toLinearMap.map_zero
  map_add' a b := by
    change Q.representation (a + b) = Q.representation a + Q.representation b
    apply LinearMap.ext
    intro f
    refine Submodule.Quotient.induction_on Q.lower.toSubmodule f ?_
    intro v
    change Q.projection (Q.upper.operatorAction (a + b) v) =
      Q.projection (Q.upper.operatorAction a v) + Q.projection (Q.upper.operatorAction b v)
    have ha : Q.upper.operatorAction (a + b) =
        Q.upper.operatorAction a + Q.upper.operatorAction b :=
      Q.upper.operatorAction.map_add' a b
    exact (congrArg (fun m : Module.End ℂ Q.upper.Space => Q.projection (m v)) ha).trans
      (Q.projection.toLinearMap.map_add _ _)
  commutes' c := by
    change Q.representation (algebraMap ℂ _ c) = algebraMap ℂ (Module.End ℂ Q.Space) c
    apply LinearMap.ext
    intro f
    refine Submodule.Quotient.induction_on Q.lower.toSubmodule f ?_
    intro v
    change Q.projection (Q.upper.operatorAction (algebraMap ℂ _ c) v) =
      c • Q.projection v
    have hc : Q.upper.operatorAction (algebraMap ℂ _ c) =
        algebraMap ℂ (Module.End ℂ Q.upper.Space) c :=
      Q.upper.operatorAction.commutes' c
    exact (congrArg (fun m : Module.End ℂ Q.upper.Space => Q.projection (m v)) hc).trans
      (Q.projection.toLinearMap.map_smul c v)

def finiteRepresentation : Representation ℂ (FiniteAdelicGL F n) Q.Space :=
  Q.representation.comp (finiteOperator F n)

def compactRepresentation : Representation ℂ (standardInfiniteCompact F n) Q.Space :=
  Q.representation.comp (compactOperator F n)

/-- This is the induced action of the existing genuine enveloping differentials. -/
def envelopingAction :
    ArchimedeanGL.EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ Q.Space :=
  Q.operatorAction.comp (differentialOperator F n)

/-- The same canonical projection intertwines finite translations. -/
def finiteProjection : Q.upper.finiteRepresentation.IntertwiningMap Q.finiteRepresentation where
  toLinearMap := Q.projection.toLinearMap
  isIntertwining' d := Q.projection.isIntertwining' (finiteOperator F n d)

theorem finiteRepresentation_isSmooth : Langlands.IsSmooth Q.finiteRepresentation :=
  Langlands.isSmooth_of_surjective Q.finiteProjection Q.projection_surjective
    Q.upper.finiteRepresentation_isSmooth

/-- The actual finite quotient as an object of the existing smooth category. -/
def smoothRepresentation : Langlands.SmoothRep ℂ (FiniteAdelicGL F n) :=
  Langlands.SmoothRep.of Q.finiteRepresentation Q.finiteRepresentation_isSmooth

/-- Local restriction retains the whole quotient carrier. -/
def localRepresentation (v : FinitePlace F) :
    Representation ℂ (FiniteLocalGL F n v) Q.Space :=
  Q.finiteRepresentation.comp (FiniteAdelicGL.localInclusion F n v).toMonoidHom

theorem localRepresentation_isSmooth (v : FinitePlace F) :
    Langlands.IsSmooth (Q.localRepresentation v) :=
  Langlands.isSmooth_comp (FiniteAdelicGL.localInclusion F n v).toMonoidHom
    (FiniteAdelicGL.localInclusion F n v).continuous Q.finiteRepresentation_isSmooth

@[simp] theorem finiteRepresentation_projection (d : FiniteAdelicGL F n)
    (f : Q.upper.Space) :
    Q.finiteRepresentation d (Q.projection f) =
      Q.projection (Q.upper.finiteRepresentation d f) := rfl

@[simp] theorem compactRepresentation_projection (k : standardInfiniteCompact F n)
    (f : Q.upper.Space) :
    Q.compactRepresentation k (Q.projection f) =
      Q.projection (Q.upper.compactRepresentation k f) := rfl

@[simp] theorem envelopingAction_projection (a : ArchimedeanGL.EnvelopingAlgebra F n)
    (f : Q.upper.Space) :
    Q.envelopingAction a (Q.projection f) =
      Q.projection (Q.upper.envelopingAction a f) := rfl

/-- Finite translation and every induced genuine differential commute on the quotient. -/
theorem finiteRepresentation_envelopingAction (d : FiniteAdelicGL F n)
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (f : Q.Space) :
    Q.finiteRepresentation d (Q.envelopingAction a f) =
      Q.envelopingAction a (Q.finiteRepresentation d f) := by
  refine Submodule.Quotient.induction_on Q.lower.toSubmodule f ?_
  intro v
  change Q.projection
      (Q.upper.finiteRepresentation d (Q.upper.envelopingAction a v)) =
    Q.projection (Q.upper.envelopingAction a (Q.upper.finiteRepresentation d v))
  exact congrArg Q.projection (Q.upper.finiteRepresentation_envelopingAction d a v)

section Descent

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (automorphicOperatorAlgebra F n) V}

/-- Descend any whole-operator intertwiner which kills the actual denominator. -/
def lift (L : Q.upper.representation.IntertwiningMap ρ) (h : Q.lower ≤ L.ker) :
    Q.representation.IntertwiningMap ρ where
  toLinearMap := Q.lower.toSubmodule.liftQ L.toLinearMap h
  isIntertwining' a := by
    change (Q.lower.toSubmodule.liftQ L.toLinearMap h).comp (Q.representation a) =
      (ρ a).comp (Q.lower.toSubmodule.liftQ L.toLinearMap h)
    apply LinearMap.ext
    intro f
    refine Submodule.Quotient.induction_on Q.lower.toSubmodule f ?_
    intro v
    change L (Q.upper.representation a v) = ρ a (L v)
    exact Representation.IntertwiningMap.isIntertwining _ _ L a v

@[simp] theorem lift_projection
    (L : Q.upper.representation.IntertwiningMap ρ) (h : Q.lower ≤ L.ker)
    (f : Q.upper.Space) :
    Q.lift L h (Q.projection f) = L f := rfl

theorem lift_unique
    (L : Q.upper.representation.IntertwiningMap ρ) (h : Q.lower ≤ L.ker)
    (M : Q.representation.IntertwiningMap ρ)
    (hM : ∀ f, M (Q.projection f) = L f) : M = Q.lift L h := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  obtain ⟨v, rfl⟩ := Q.projection_surjective f
  exact hM v

end Descent

/-- Irreducibility concerns every concrete operator on the actual quotient. -/
abbrev IsIrreducible : Prop := Q.representation.IsIrreducible

/-- Quotient classes distinguish representation equivalence from presentation equality. -/
abbrev Equivalence (T : OperatorSubquotient F n) :=
  Q.representation.Equiv T.representation

/-- Forget extra operators without changing the equivariant linear equivalence. -/
def Equivalence.finiteRestriction {Q T : OperatorSubquotient F n} (e : Q.Equivalence T) :
    Q.finiteRepresentation.Equiv T.finiteRepresentation :=
  Representation.Equiv.mk e.toLinearEquiv
    (fun d => e.toIntertwiningMap.isIntertwining' (finiteOperator F n d))

variable (F n)

def equivalenceSetoid : Setoid (OperatorSubquotient F n) where
  r Q T := Nonempty (Q.Equivalence T)
  iseqv :=
    ⟨fun Q => ⟨Representation.Equiv.refl Q.representation⟩,
      fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- Classes of genuine quotient representations, retaining every concrete operator. -/
def IsoClass := Quotient (equivalenceSetoid F n)

variable {F n}

def isoClass : IsoClass F n := Quotient.mk (equivalenceSetoid F n) Q

theorem isoClass_eq_iff (T : OperatorSubquotient F n) :
    Q.isoClass = T.isoClass ↔ Nonempty (Q.Equivalence T) :=
  Quotient.eq

/-- A whole-operator quotient class has a well-defined finite smooth class. -/
def IsoClass.finiteClass (c : IsoClass F n) :
    Langlands.SmoothRep.IsoClass.{0, uF, uF} ℂ (FiniteAdelicGL F n) :=
  Quotient.lift (s := equivalenceSetoid F n)
    (fun Q : OperatorSubquotient F n => Langlands.SmoothRep.isoClass Q.smoothRepresentation)
    (fun _ _ ⟨e⟩ => (Langlands.SmoothRep.isoClass_eq_iff _ _).mpr
      ⟨Langlands.SmoothRep.mkIso e.finiteRestriction⟩) c

@[simp] theorem finiteClass_isoClass :
    Q.isoClass.finiteClass = Langlands.SmoothRep.isoClass Q.smoothRepresentation := rfl

end OperatorSubquotient

/-- Every existing actual realization supplies its genuine zero-denominator quotient. -/
def OperatorRealization.toSubquotient (S : OperatorRealization F n) :
    OperatorSubquotient F n := ⟨S, ⊥⟩

/-- The canonical projection identifies this quotient with its original realization. -/
def OperatorRealization.toSubquotientEquiv (S : OperatorRealization F n) :
    S.representation.Equiv S.toSubquotient.representation :=
  S.toSubquotient.projection.ofBijective ⟨by
    apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_mkQ _, S.toSubquotient.projection_surjective⟩

end Langlands.Automorphic
