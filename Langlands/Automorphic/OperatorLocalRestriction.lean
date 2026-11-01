import Langlands.Automorphic.OperatorZeroDenominator
import Langlands.Automorphic.LocalRealization

/-! # Whole-carrier local smooth restrictions of actual operator quotients -/

noncomputable section
universe uF uV
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace Langlands.Global.FiniteAdelicGL

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ) (v : FinitePlace F)

/-- Restrict along the actual continuous local inclusion, keeping the carrier and maps. -/
def localRestrictionFunctor :
    Langlands.SmoothRep.{0, uF, uV} ℂ (FiniteAdelicGL F n) ⥤
      Langlands.SmoothRep.{0, uF, uV} ℂ (FiniteLocalGL F n v) :=
  (Langlands.smoothRepProperty ℂ (FiniteLocalGL F n v)).lift
    (Langlands.SmoothRep.toRep ⋙ Rep.resFunctor (localInclusion F n v).toMonoidHom)
    (fun A => Langlands.isSmooth_comp (localInclusion F n v).toMonoidHom
      (localInclusion F n v).continuous A.isSmooth)

@[simp] theorem localRestrictionFunctor_representation
    (A : Langlands.SmoothRep.{0, uF, uV} ℂ (FiniteAdelicGL F n)) :
    ((localRestrictionFunctor F n v).obj A).representation =
      A.representation.comp (localInclusion F n v).toMonoidHom := rfl

@[simp] theorem localRestrictionFunctor_map_apply
    {A B : Langlands.SmoothRep.{0, uF, uV} ℂ (FiniteAdelicGL F n)}
    (f : A ⟶ B) (x : A) :
    Langlands.SmoothRep.hom ((localRestrictionFunctor F n v).map f) x =
      Langlands.SmoothRep.hom f x := rfl

/-- Local restriction descends to the genuine categorical isomorphism quotient. -/
def localRestrictionClass
    (c : Langlands.SmoothRep.IsoClass.{0, uF, uV} ℂ (FiniteAdelicGL F n)) :
    Langlands.SmoothRep.IsoClass.{0, uF, uV} ℂ (FiniteLocalGL F n v) :=
  Quotient.lift
    (fun A => Langlands.SmoothRep.isoClass ((localRestrictionFunctor F n v).obj A))
    (fun _ _ h => (Langlands.SmoothRep.isoClass_eq_iff _ _).mpr
      ⟨(localRestrictionFunctor F n v).mapIso (Classical.choice h)⟩) c

@[simp] theorem localRestrictionClass_isoClass
    (A : Langlands.SmoothRep.{0, uF, uV} ℂ (FiniteAdelicGL F n)) :
    localRestrictionClass F n v (Langlands.SmoothRep.isoClass A) =
      Langlands.SmoothRep.isoClass ((localRestrictionFunctor F n v).obj A) := rfl

end Langlands.Global.FiniteAdelicGL

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance localRestrictionRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance localRestrictionContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance localRestrictionSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance localRestrictionFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance localRestrictionStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance localRestrictionRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n) (v : FinitePlace F)

/-- Local restriction of the whole actual realization carrier. -/
def localRepresentation : Representation ℂ (FiniteLocalGL F n v) S.Space :=
  S.finiteRepresentation.comp (FiniteAdelicGL.localInclusion F n v).toMonoidHom

theorem localRepresentation_isSmooth : Langlands.IsSmooth (S.localRepresentation v) :=
  Langlands.isSmooth_comp (FiniteAdelicGL.localInclusion F n v).toMonoidHom
    (FiniteAdelicGL.localInclusion F n v).continuous S.finiteRepresentation_isSmooth

def localSmoothRepresentation : Langlands.SmoothRep ℂ (FiniteLocalGL F n v) :=
  Langlands.SmoothRep.of (S.localRepresentation v) (S.localRepresentation_isSmooth v)

/-- The existing faithful finite image identifies the local restriction with actual forms. -/
def localFormEquiv :
    (S.localRepresentation v).Equiv (S.toFiniteRealization.toLocal F n v).representation :=
  Representation.Equiv.mk S.finiteEquiv.toLinearEquiv
    (fun g => S.finiteEquiv.toIntertwiningMap.isIntertwining'
      (FiniteAdelicGL.localInclusion F n v g))

@[simp] theorem localFormEquiv_apply (f : S.Space) :
    S.localFormEquiv v f = S.finiteEquiv f := rfl

end OperatorRealization

namespace OperatorSubquotient

variable (Q : OperatorSubquotient F n) (v : FinitePlace F)

/-- Bundle the already proved smooth local restriction of the actual module quotient. -/
def localSmoothRepresentation : Langlands.SmoothRep ℂ (FiniteLocalGL F n v) :=
  Langlands.SmoothRep.of (Q.localRepresentation v) (Q.localRepresentation_isSmooth v)

@[simp] theorem localRestrictionFunctor_smoothRepresentation :
    (FiniteAdelicGL.localRestrictionFunctor F n v).obj Q.smoothRepresentation =
      Q.localSmoothRepresentation v := rfl

/-- The actual canonical projection also intertwines every local translation. -/
def localProjection :
    (Q.upper.localRepresentation v).IntertwiningMap (Q.localRepresentation v) where
  toLinearMap := Q.projection.toLinearMap
  isIntertwining' g := Q.finiteProjection.isIntertwining'
    (FiniteAdelicGL.localInclusion F n v g)

@[simp] theorem localProjection_apply (f : Q.upper.Space) :
    Q.localProjection v f = Q.projection f := rfl

theorem localProjection_surjective : Function.Surjective (Q.localProjection v) :=
  Q.projection_surjective

@[simp] theorem localProjection_ker_toSubmodule :
    (Q.localProjection v).ker.toSubmodule = Q.lower.toSubmodule :=
  Submodule.ker_mkQ _

@[simp] theorem localRepresentation_projection (g : FiniteLocalGL F n v)
    (f : Q.upper.Space) :
    Q.localRepresentation v g (Q.projection f) =
      Q.projection (Q.upper.localRepresentation v g f) := rfl

/-- Quotient intertwiners refer to every concrete operator before restriction. -/
abbrev Intertwiner (T : OperatorSubquotient F n) :=
  Q.representation.IntertwiningMap T.representation

namespace Intertwiner

variable {Q T U : OperatorSubquotient F n}

/-- Forget operators, keeping exactly the supplied quotient linear map. -/
def localRestriction (L : Q.Intertwiner T) (v : FinitePlace F) :
    (Q.localRepresentation v).IntertwiningMap (T.localRepresentation v) where
  toLinearMap := L.toLinearMap
  isIntertwining' g := L.isIntertwining'
    (finiteOperator F n (FiniteAdelicGL.localInclusion F n v g))

@[simp] theorem localRestriction_apply (L : Q.Intertwiner T) (v : FinitePlace F)
    (f : Q.Space) : L.localRestriction v f = L f := rfl

/-- Restriction is complex-linear and faithful on the supplied whole-action Hom space. -/
def localRestrictionLinearMap (Q T : OperatorSubquotient F n) (v : FinitePlace F) :
    (Q.Intertwiner T) →ₗ[ℂ]
      ((Q.localRepresentation v).IntertwiningMap (T.localRepresentation v)) where
  toFun L := L.localRestriction v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem localRestriction_injective (v : FinitePlace F) :
    Function.Injective (localRestriction (Q := Q) (T := T) · v) := by
  intro L M h
  apply Representation.IntertwiningMap.ext
  exact congrArg (fun m :
    (Q.localRepresentation v).IntertwiningMap (T.localRepresentation v) =>
      m.toLinearMap) h

@[simp] theorem localRestriction_id (Q : OperatorSubquotient F n) (v : FinitePlace F) :
    localRestriction (Q := Q) (T := Q)
        (Representation.IntertwiningMap.id Q.representation) v =
      Representation.IntertwiningMap.id (Q.localRepresentation v) := rfl

theorem localRestriction_comp (M : T.Intertwiner U) (L : Q.Intertwiner T)
    (v : FinitePlace F) :
    localRestriction (Q := Q) (T := U) (M.comp L) v =
      (M.localRestriction v).comp (L.localRestriction v) :=
  rfl

end Intertwiner

namespace Equivalence

variable {Q T : OperatorSubquotient F n}

/-- A genuine whole-action equivalence restricts on the same quotient carriers. -/
def localRestriction (e : Q.Equivalence T) (v : FinitePlace F) :
    (Q.localRepresentation v).Equiv (T.localRepresentation v) :=
  Representation.Equiv.mk e.toLinearEquiv
    (fun g => e.toIntertwiningMap.isIntertwining'
      (finiteOperator F n (FiniteAdelicGL.localInclusion F n v g)))

@[simp] theorem localRestriction_toIntertwiningMap (e : Q.Equivalence T)
    (v : FinitePlace F) :
    (e.localRestriction v).toIntertwiningMap =
      Intertwiner.localRestriction e.toIntertwiningMap v := rfl

end Equivalence

/-- Class restriction factors through the published finite smooth class. -/
def IsoClass.localClass (c : IsoClass F n) (v : FinitePlace F) :
    Langlands.SmoothRep.IsoClass.{0, uF, uF} ℂ (FiniteLocalGL F n v) :=
  FiniteAdelicGL.localRestrictionClass F n v c.finiteClass

@[simp] theorem localClass_isoClass :
    Q.isoClass.localClass v = Langlands.SmoothRep.isoClass (Q.localSmoothRepresentation v) :=
  rfl

end OperatorSubquotient

namespace OperatorRealization

variable (S : OperatorRealization F n) (v : FinitePlace F)

/-- Restrict the genuine zero-denominator projection equivalence to the local action. -/
def toSubquotientLocalEquiv :
    (S.localRepresentation v).Equiv (S.toSubquotient.localRepresentation v) :=
  Representation.Equiv.mk (OperatorRealization.toSubquotientEquiv F n S).toLinearEquiv
    (fun g => (OperatorRealization.toSubquotientEquiv F n S).toIntertwiningMap.isIntertwining'
      (finiteOperator F n (FiniteAdelicGL.localInclusion F n v g)))

@[simp] theorem toSubquotientLocalEquiv_apply (f : S.Space) :
    S.toSubquotientLocalEquiv v f = S.toSubquotient.projection f := rfl

/-- Local forgetting of an actual realization class through its existing finite image. -/
def IsoClass.localClass (c : IsoClass F n) (v : FinitePlace F) :
    Langlands.SmoothRep.IsoClass.{0, uF, uF} ℂ (FiniteLocalGL F n v) :=
  FiniteAdelicGL.localRestrictionClass F n v c.finiteClass

@[simp] theorem localClass_isoClass :
    S.isoClass.localClass v = Langlands.SmoothRep.isoClass (S.localSmoothRepresentation v) := by
  exact (Langlands.SmoothRep.isoClass_eq_iff _ _).mpr
    ⟨Langlands.SmoothRep.mkIso (S.localFormEquiv v).symm⟩

/-- The canonical zero-denominator class embedding commutes with local restriction. -/
@[simp] theorem IsoClass.localClass_toSubquotient (c : IsoClass F n)
    (v : FinitePlace F) :
    c.toSubquotient.localClass v = c.localClass v := by
  change FiniteAdelicGL.localRestrictionClass F n v c.toSubquotient.finiteClass =
    FiniteAdelicGL.localRestrictionClass F n v c.finiteClass
  rw [finiteClass_toSubquotient]

end OperatorRealization
end Langlands.Automorphic
