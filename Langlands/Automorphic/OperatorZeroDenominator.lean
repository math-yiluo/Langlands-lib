import Langlands.Automorphic.OperatorSubquotient

/-! # Realizations and their actual zero-denominator quotients -/

noncomputable section
universe uF
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance zeroQuotientRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance zeroQuotientContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance zeroQuotientSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance zeroQuotientFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance zeroQuotientStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance zeroQuotientRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization

@[simp] theorem toSubquotientEquiv_apply (S : OperatorRealization F n) (f : S.Space) :
    (OperatorRealization.toSubquotientEquiv F n S) f = S.toSubquotient.projection f := rfl

namespace Intertwiner

variable {S T U : OperatorRealization F n}

/-- Conjugate an actual realization map by the canonical zero-quotient projections. -/
def toSubquotient (L : S.Intertwiner T) :
    S.toSubquotient.representation.IntertwiningMap T.toSubquotient.representation :=
  (OperatorRealization.toSubquotientEquiv F n T).toIntertwiningMap.comp
    (L.comp (OperatorRealization.toSubquotientEquiv F n S).symm.toIntertwiningMap)

/-- Every map of these actual quotients returns to an actual realization map. -/
def ofSubquotient
    (L : S.toSubquotient.representation.IntertwiningMap T.toSubquotient.representation) :
    S.Intertwiner T :=
  (OperatorRealization.toSubquotientEquiv F n T).symm.toIntertwiningMap.comp
    (L.comp (OperatorRealization.toSubquotientEquiv F n S).toIntertwiningMap)

@[simp] theorem toSubquotient_apply (L : S.Intertwiner T) (f : S.toSubquotient.Space) :
    L.toSubquotient f =
      (OperatorRealization.toSubquotientEquiv F n T) (L ((OperatorRealization.toSubquotientEquiv F n S).symm f)) := rfl

@[simp] theorem ofSubquotient_apply
    (L : S.toSubquotient.representation.IntertwiningMap T.toSubquotient.representation)
    (f : S.Space) :
    ofSubquotient L f =
      (OperatorRealization.toSubquotientEquiv F n T).symm (L ((OperatorRealization.toSubquotientEquiv F n S) f)) := rfl

@[simp] theorem toSubquotient_apply_projection (L : S.Intertwiner T) (f : S.Space) :
    L.toSubquotient (S.toSubquotient.projection f) = T.toSubquotient.projection (L f) :=
  congrArg (fun x => (OperatorRealization.toSubquotientEquiv F n T) (L x))
    ((OperatorRealization.toSubquotientEquiv F n S).symm_apply_apply f)

/-- The canonical projection is natural for every whole-operator realization map. -/
theorem toSubquotient_naturality (L : S.Intertwiner T) :
    L.toSubquotient.comp S.toSubquotient.projection =
      T.toSubquotient.projection.comp L := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  exact toSubquotient_apply_projection L

@[simp] theorem ofSubquotient_toSubquotient (L : S.Intertwiner T) :
    ofSubquotient L.toSubquotient = L := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  change (OperatorRealization.toSubquotientEquiv F n T).symm
      ((OperatorRealization.toSubquotientEquiv F n T) (L ((OperatorRealization.toSubquotientEquiv F n S).symm ((OperatorRealization.toSubquotientEquiv F n S) f)))) =
    L f
  exact ((OperatorRealization.toSubquotientEquiv F n T).symm_apply_apply _).trans
    (congrArg L ((OperatorRealization.toSubquotientEquiv F n S).symm_apply_apply f))

@[simp] theorem toSubquotient_ofSubquotient
    (L : S.toSubquotient.representation.IntertwiningMap T.toSubquotient.representation) :
    toSubquotient (S := S) (T := T) (ofSubquotient L) = L := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  change (OperatorRealization.toSubquotientEquiv F n T)
      ((OperatorRealization.toSubquotientEquiv F n T).symm (L ((OperatorRealization.toSubquotientEquiv F n S) ((OperatorRealization.toSubquotientEquiv F n S).symm f)))) =
    L f
  exact ((OperatorRealization.toSubquotientEquiv F n T).apply_symm_apply _).trans
    (congrArg L ((OperatorRealization.toSubquotientEquiv F n S).apply_symm_apply f))

/-- The zero-denominator construction identifies the entire complex-linear map spaces. -/
def toSubquotientLinearEquiv (S T : OperatorRealization F n) :
    (S.Intertwiner T) ≃ₗ[ℂ]
      (S.toSubquotient.representation.IntertwiningMap T.toSubquotient.representation) where
  toFun := toSubquotient
  invFun := ofSubquotient
  left_inv := ofSubquotient_toSubquotient
  right_inv := toSubquotient_ofSubquotient
  map_add' L M := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    change (OperatorRealization.toSubquotientEquiv F n T)
        (L ((OperatorRealization.toSubquotientEquiv F n S).symm f) + M ((OperatorRealization.toSubquotientEquiv F n S).symm f)) =
      (OperatorRealization.toSubquotientEquiv F n T) (L ((OperatorRealization.toSubquotientEquiv F n S).symm f)) +
        (OperatorRealization.toSubquotientEquiv F n T) (M ((OperatorRealization.toSubquotientEquiv F n S).symm f))
    exact (OperatorRealization.toSubquotientEquiv F n T).map_add _ _
  map_smul' c L := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    change (OperatorRealization.toSubquotientEquiv F n T) (c • L ((OperatorRealization.toSubquotientEquiv F n S).symm f)) =
      c • (OperatorRealization.toSubquotientEquiv F n T) (L ((OperatorRealization.toSubquotientEquiv F n S).symm f))
    exact (OperatorRealization.toSubquotientEquiv F n T).map_smul c _

@[simp] theorem toSubquotientLinearEquiv_apply (L : S.Intertwiner T) :
    toSubquotientLinearEquiv S T L = L.toSubquotient := rfl

@[simp] theorem toSubquotientLinearEquiv_symm_apply
    (L : S.toSubquotient.representation.IntertwiningMap T.toSubquotient.representation) :
    (toSubquotientLinearEquiv S T).symm L = ofSubquotient L := rfl

@[simp] theorem toSubquotient_id (S : OperatorRealization F n) :
    toSubquotient (Representation.IntertwiningMap.id S.representation) =
      Representation.IntertwiningMap.id S.toSubquotient.representation := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  exact (OperatorRealization.toSubquotientEquiv F n S).apply_symm_apply f

theorem toSubquotient_comp (M : T.Intertwiner U) (L : S.Intertwiner T) :
    toSubquotient (S := S) (T := U) (M.comp L) = M.toSubquotient.comp L.toSubquotient := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  change (OperatorRealization.toSubquotientEquiv F n U) (M (L ((OperatorRealization.toSubquotientEquiv F n S).symm f))) =
    (OperatorRealization.toSubquotientEquiv F n U)
      (M ((OperatorRealization.toSubquotientEquiv F n T).symm
        ((OperatorRealization.toSubquotientEquiv F n T) (L ((OperatorRealization.toSubquotientEquiv F n S).symm f)))))
  exact congrArg (fun x => (OperatorRealization.toSubquotientEquiv F n U) (M x))
    ((OperatorRealization.toSubquotientEquiv F n T).symm_apply_apply _).symm

theorem toSubquotient_bijective :
    Function.Bijective (toSubquotient (S := S) (T := T)) :=
  (toSubquotientLinearEquiv S T).bijective

@[simp] theorem toSubquotient_eq_iff (L M : S.Intertwiner T) :
    L.toSubquotient = M.toSubquotient ↔ L = M :=
  (toSubquotientLinearEquiv S T).injective.eq_iff

end Intertwiner

namespace Equivalence

variable {S T : OperatorRealization F n}

/-- A supplied whole-action equivalence induces an actual zero-quotient equivalence. -/
def toSubquotient (e : S.Equivalence T) : S.toSubquotient.Equivalence T.toSubquotient :=
  (OperatorRealization.toSubquotientEquiv F n S).symm.trans (e.trans (OperatorRealization.toSubquotientEquiv F n T))

@[simp] theorem toSubquotient_toIntertwiningMap (e : S.Equivalence T) :
    e.toSubquotient.toIntertwiningMap =
      Intertwiner.toSubquotient (S := S) (T := T) e.toIntertwiningMap := rfl

@[simp] theorem toSubquotient_apply_projection (e : S.Equivalence T) (f : S.Space) :
    e.toSubquotient (S.toSubquotient.projection f) = T.toSubquotient.projection (e f) :=
  Intertwiner.toSubquotient_apply_projection e.toIntertwiningMap f

end Equivalence

/-- Zero-denominator quotienting preserves and reflects genuine whole-action equivalence. -/
theorem toSubquotient_equivalence_iff (S T : OperatorRealization F n) :
    Nonempty (S.toSubquotient.Equivalence T.toSubquotient) ↔ Nonempty (S.Equivalence T) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨(OperatorRealization.toSubquotientEquiv F n S).trans (e.trans (OperatorRealization.toSubquotientEquiv F n T).symm)⟩
  · rintro ⟨e⟩
    exact ⟨e.toSubquotient⟩

/-- All invariant subspaces correspond through the actual canonical projection. -/
def toSubquotientSubrepresentationOrderIso (S : OperatorRealization F n) :
    Subrepresentation S.representation ≃o Subrepresentation S.toSubquotient.representation :=
  conjugatedSubrepresentationOrderIso S.representation S.toSubquotient.representation
    (MulEquiv.refl _) (OperatorRealization.toSubquotientEquiv F n S).toLinearEquiv
    (fun a f => (Representation.IntertwiningMap.isIntertwining _ _
      (OperatorRealization.toSubquotientEquiv F n S).toIntertwiningMap a f).symm)

theorem toSubquotient_isIrreducible_iff (S : OperatorRealization F n) :
    S.toSubquotient.IsIrreducible ↔ S.IsIrreducible :=
  S.toSubquotientSubrepresentationOrderIso.isSimpleOrder_iff.symm

/-- Restrict the canonical whole-action equivalence to the actual finite action. -/
def toSubquotientFiniteEquiv (S : OperatorRealization F n) :
    S.finiteRepresentation.Equiv S.toSubquotient.finiteRepresentation :=
  Representation.Equiv.mk (OperatorRealization.toSubquotientEquiv F n S).toLinearEquiv
    (fun d => (OperatorRealization.toSubquotientEquiv F n S).toIntertwiningMap.isIntertwining' (finiteOperator F n d))

namespace IsoClass

/-- Classes of actual realized spaces embed into classes of actual operator quotients. -/
def toSubquotient (c : IsoClass F n) : OperatorSubquotient.IsoClass F n :=
  Quotient.lift (s := equivalenceSetoid F n) (fun S => S.toSubquotient.isoClass)
    (fun S T h => (S.toSubquotient.isoClass_eq_iff T.toSubquotient).mpr
      ((toSubquotient_equivalence_iff S T).mpr h)) c

@[simp] theorem toSubquotient_isoClass (S : OperatorRealization F n) :
    toSubquotient S.isoClass = S.toSubquotient.isoClass := rfl

theorem toSubquotient_injective :
    Function.Injective (toSubquotient (F := F) (n := n)) := by
  intro c d
  refine Quotient.inductionOn₂ c d ?_
  intro S T h
  exact (S.isoClass_eq_iff T).mpr
    ((toSubquotient_equivalence_iff S T).mp
      ((S.toSubquotient.isoClass_eq_iff T.toSubquotient).mp h))

/-- The class embedding retains the whole-action equality criterion. -/
def toSubquotientEmbedding : IsoClass F n ↪ OperatorSubquotient.IsoClass F n :=
  ⟨toSubquotient, toSubquotient_injective⟩

@[simp] theorem toSubquotient_eq_iff (c d : IsoClass F n) :
    toSubquotient c = toSubquotient d ↔ c = d := toSubquotient_injective.eq_iff

/-- Passing to the finite smooth class commutes with the actual zero quotient. -/
@[simp] theorem finiteClass_toSubquotient (c : IsoClass F n) :
    (toSubquotient c).finiteClass = c.finiteClass := by
  refine Quotient.inductionOn c ?_
  intro S
  exact (Langlands.SmoothRep.isoClass_eq_iff _ _).mpr
    ⟨Langlands.SmoothRep.mkIso
      (S.toSubquotientFiniteEquiv.symm.trans S.finiteEquiv)⟩

end IsoClass
end OperatorRealization
end Langlands.Automorphic
