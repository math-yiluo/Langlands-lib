import Langlands.Algebra.NondegenerateModuleAdditive
import Langlands.Algebra.IdempotentedRingRightLimitAction
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# The original forgetful functor and its canonical natural endomorphisms

Renard I.1.6, printed pp.11–12/PDF17–18. The map from completed-ring
families uses the published action on each original nondegenerate module.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open CategoryTheory

universe uA uM uN

/-- Forget only the original action, retaining the entire original additive map. -/
def nonUnitalModuleForgetful (A : Type uA) [NonUnitalRing A] :
    NonUnitalModuleCat.{uA, uM} A ⥤ AddCommGrpCat.{uM} where
  obj M := AddCommGrpCat.of M
  map f := AddCommGrpCat.ofHom f.toAddMonoidHom
  map_id _ := rfl
  map_comp _ _ := rfl

instance nonUnitalModuleForgetful_additive (A : Type uA) [NonUnitalRing A] :
    (nonUnitalModuleForgetful.{uA, uM} A).Additive where
  map_add := by intros; rfl

@[simp] theorem nonUnitalModuleForgetful_obj (A : Type uA) [NonUnitalRing A]
    (M : NonUnitalModuleCat.{uA, uM} A) :
    (nonUnitalModuleForgetful A).obj M = AddCommGrpCat.of M := rfl

theorem nonUnitalModuleForgetful_obj_carrier (A : Type uA) [NonUnitalRing A]
    (M : NonUnitalModuleCat.{uA, uM} A) :
    ((nonUnitalModuleForgetful A).obj M : Type uM) = (M : Type uM) := rfl

@[simp] theorem nonUnitalModuleForgetful_map (A : Type uA) [NonUnitalRing A]
    {M N : NonUnitalModuleCat.{uA, uM} A} (f : M ⟶ N) :
    (nonUnitalModuleForgetful A).map f = AddCommGrpCat.ofHom f.toAddMonoidHom := rfl

@[simp] theorem nonUnitalModuleForgetful_map_hom (A : Type uA) [NonUnitalRing A]
    {M N : NonUnitalModuleCat.{uA, uM} A} (f : M ⟶ N) :
    ((nonUnitalModuleForgetful A).map f).hom = f.toAddMonoidHom := rfl

@[simp] theorem nonUnitalModuleForgetful_map_apply (A : Type uA) [NonUnitalRing A]
    {M N : NonUnitalModuleCat.{uA, uM} A} (f : M ⟶ N) (m : M) :
    (nonUnitalModuleForgetful A).map f m = f.toAddMonoidHom m := rfl

/-- Renard's forgetful functor is the actual inclusion followed by forgetting. -/
def nondegenerateModuleForgetful (A : Type uA) [NonUnitalRing A] :
    NondegenerateModuleCat.{uA, uM} A ⥤ AddCommGrpCat.{uM} :=
  nondegenerateInclusion A ⋙ nonUnitalModuleForgetful A

instance nondegenerateModuleForgetful_additive (A : Type uA) [NonUnitalRing A] :
    (nondegenerateModuleForgetful.{uA, uM} A).Additive :=
  inferInstanceAs ((nondegenerateInclusion A ⋙ nonUnitalModuleForgetful A).Additive)

theorem nondegenerateModuleForgetful_eq (A : Type uA) [NonUnitalRing A] :
    nondegenerateModuleForgetful.{uA, uM} A =
      nondegenerateInclusion A ⋙ nonUnitalModuleForgetful A := rfl

@[simp] theorem nondegenerateModuleForgetful_obj (A : Type uA) [NonUnitalRing A]
    (M : NondegenerateModuleCat.{uA, uM} A) :
    (nondegenerateModuleForgetful A).obj M = AddCommGrpCat.of M.obj := rfl

theorem nondegenerateModuleForgetful_obj_carrier (A : Type uA) [NonUnitalRing A]
    (M : NondegenerateModuleCat.{uA, uM} A) :
    ((nondegenerateModuleForgetful A).obj M : Type uM) = (M.obj : Type uM) := rfl

@[simp] theorem nondegenerateModuleForgetful_map (A : Type uA) [NonUnitalRing A]
    {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N) :
    (nondegenerateModuleForgetful A).map f =
      AddCommGrpCat.ofHom f.hom.toAddMonoidHom := rfl

@[simp] theorem nondegenerateModuleForgetful_map_hom (A : Type uA) [NonUnitalRing A]
    {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N) :
    ((nondegenerateModuleForgetful A).map f).hom = f.hom.toAddMonoidHom := rfl

@[simp] theorem nondegenerateModuleForgetful_map_apply (A : Type uA) [NonUnitalRing A]
    {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N) (m : M.obj) :
    (nondegenerateModuleForgetful A).map f m = f.hom.toAddMonoidHom m := rfl

/-- Actual natural transformations, with their inherited categorical endomorphism ring. -/
abbrev NondegenerateModuleNaturalEnd (A : Type uA) [NonUnitalRing A] :=
  End (nondegenerateModuleForgetful.{uA, uM} A)

namespace NondegenerateModuleNaturalEnd

variable {A : Type uA} [NonUnitalRing A]

/-- The named ring is exactly the inherited ring of actual natural transformations. -/
@[instance_reducible]
def ring (A : Type uA) [NonUnitalRing A] :
    Ring (NondegenerateModuleNaturalEnd.{uA, uM} A) :=
  inferInstanceAs (Ring (End (nondegenerateModuleForgetful.{uA, uM} A)))

@[simp] theorem zero_app_hom (M : NondegenerateModuleCat.{uA, uM} A) :
    ((0 : NondegenerateModuleNaturalEnd A).app M).hom = 0 := rfl

@[simp] theorem add_app_hom (θ η : NondegenerateModuleNaturalEnd.{uA, uM} A)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    ((θ + η).app M).hom = (θ.app M).hom + (η.app M).hom := rfl

@[simp] theorem one_app_hom (M : NondegenerateModuleCat.{uA, uM} A) :
    ((1 : NondegenerateModuleNaturalEnd A).app M).hom = AddMonoidHom.id M.obj := rfl

/-- Multiplication applies the right factor first, then the left factor. -/
@[simp] theorem mul_app_hom (θ η : NondegenerateModuleNaturalEnd.{uA, uM} A)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    ((θ * η).app M).hom = (θ.app M).hom.comp (η.app M).hom := rfl

end NondegenerateModuleNaturalEnd

namespace IdempotentedRingRightLimit

variable {A : Type uA} [NonUnitalRing A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]

/-- The published action bundled as the full additive component on an original module. -/
def actionAddHom (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (x : IdempotentedRingRightLimit A) : M →+ M where
  toFun := IdempotentedRingRightLimitAction.act hM x
  map_zero' := IdempotentedRingRightLimitAction.act_zero hA hM x
  map_add' := IdempotentedRingRightLimitAction.act_add hA hM x

@[simp] theorem actionAddHom_apply (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (x : IdempotentedRingRightLimit A) (m : M) :
    actionAddHom hA hM x m = IdempotentedRingRightLimitAction.act hM x m := rfl

theorem actionAddHom_coe (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (x : IdempotentedRingRightLimit A) :
    ⇑(actionAddHom hA hM x) = IdempotentedRingRightLimitAction.act hM x := rfl

theorem actionAddHom_eq (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (x : IdempotentedRingRightLimit A) (m : M) (e : Idempotent A)
    (he : (e : A) • m = m) :
    actionAddHom hA hM x m = x.val e • m :=
  IdempotentedRingRightLimitAction.act_eq hA hM x m e he

@[simp] theorem actionAddHom_canonical (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (a : A) :
    actionAddHom hA hM (canonical a) =
      NonUnitalModule.toEndHom (inferInstance : NonUnitalModule A M) a := by
  apply AddMonoidHom.ext
  exact IdempotentedRingRightLimitAction.canonical_act hA hM a

@[simp] theorem actionAddHom_zero (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    actionAddHom hA hM 0 = 0 := by
  apply AddMonoidHom.ext
  exact IdempotentedRingRightLimitAction.zero_act hA hM

theorem actionAddHom_add (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (x y : IdempotentedRingRightLimit A) :
    actionAddHom hA hM (x + y) = actionAddHom hA hM x + actionAddHom hA hM y := by
  apply AddMonoidHom.ext
  exact IdempotentedRingRightLimitAction.add_act hA hM x y

@[simp] theorem actionAddHom_unit (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    actionAddHom hA hM unit = AddMonoidHom.id M := by
  apply AddMonoidHom.ext
  exact IdempotentedRingRightLimitAction.unit_act hA hM

theorem actionAddHom_product (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (x y : IdempotentedRingRightLimit A) :
    actionAddHom hA hM (product hA x y) =
      (actionAddHom hA hM x).comp (actionAddHom hA hM y) := by
  apply AddMonoidHom.ext
  exact IdempotentedRingRightLimitAction.product_act hA hM x y

variable {N : Type uN} [AddCommGroup N] [NonUnitalModule A N]

/-- Naturality as equality of entire additive maps, with independent module universes. -/
theorem actionAddHom_naturality (hA : IsIdempotented A)
    (hM : IsNondegenerate A M) (hN : IsNondegenerate A N)
    (f : NonUnitalModuleHom A M N) (x : IdempotentedRingRightLimit A) :
    f.toAddMonoidHom.comp (actionAddHom hA hM x) =
      (actionAddHom hA hN x).comp f.toAddMonoidHom := by
  apply AddMonoidHom.ext
  exact IdempotentedRingRightLimitAction.map_act hA hM hN f x

/-- Every family acts as an actual natural endomorphism of the forgetful functor. -/
def familyNaturalEnd (hA : IsIdempotented A) (x : IdempotentedRingRightLimit A) :
    NondegenerateModuleNaturalEnd.{uA, uM} A where
  app M := AddCommGrpCat.ofHom (actionAddHom hA M.property x)
  naturality M N f := by
    apply AddCommGrpCat.hom_ext
    exact (actionAddHom_naturality hA M.property N.property f.hom x).symm

@[simp] theorem familyNaturalEnd_app (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (M : NondegenerateModuleCat.{uA, uM} A) :
    (familyNaturalEnd hA x).app M = AddCommGrpCat.ofHom (actionAddHom hA M.property x) :=
  rfl

@[simp] theorem familyNaturalEnd_app_hom (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (M : NondegenerateModuleCat.{uA, uM} A) :
    ((familyNaturalEnd hA x).app M).hom = actionAddHom hA M.property x := rfl

@[simp] theorem familyNaturalEnd_app_apply (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (M : NondegenerateModuleCat.{uA, uM} A)
    (m : M.obj) :
    (familyNaturalEnd hA x).app M m = IdempotentedRingRightLimitAction.act M.property x m :=
  rfl

@[simp] theorem familyNaturalEnd_zero (hA : IsIdempotented A) :
    familyNaturalEnd.{uA, uM} hA 0 = 0 := by
  apply NatTrans.ext
  funext M
  apply AddCommGrpCat.hom_ext
  exact actionAddHom_zero hA M.property

theorem familyNaturalEnd_add (hA : IsIdempotented A)
    (x y : IdempotentedRingRightLimit A) :
    familyNaturalEnd.{uA, uM} hA (x + y) =
      familyNaturalEnd hA x + familyNaturalEnd hA y := by
  apply NatTrans.ext
  funext M
  apply AddCommGrpCat.hom_ext
  exact actionAddHom_add hA M.property x y

@[simp] theorem familyNaturalEnd_unit (hA : IsIdempotented A) :
    familyNaturalEnd.{uA, uM} hA unit = 1 := by
  apply NatTrans.ext
  funext M
  apply AddCommGrpCat.hom_ext
  exact actionAddHom_unit hA M.property

theorem familyNaturalEnd_product (hA : IsIdempotented A)
    (x y : IdempotentedRingRightLimit A) :
    familyNaturalEnd.{uA, uM} hA (product hA x y) =
      familyNaturalEnd hA x * familyNaturalEnd hA y := by
  apply NatTrans.ext
  funext M
  apply AddCommGrpCat.hom_ext
  exact actionAddHom_product hA M.property x y

/-- The canonical unital ring map into the actual natural-endomorphism ring. -/
def toNaturalEndRingHom (hA : IsIdempotented A) :
    letI := ring hA
    letI := NondegenerateModuleNaturalEnd.ring.{uA, uM} A
    IdempotentedRingRightLimit A →+* NondegenerateModuleNaturalEnd.{uA, uM} A := by
  letI := ring hA
  letI := NondegenerateModuleNaturalEnd.ring.{uA, uM} A
  exact
    { toFun := familyNaturalEnd hA
      map_zero' := familyNaturalEnd_zero hA
      map_add' := familyNaturalEnd_add hA
      map_one' := familyNaturalEnd_unit hA
      map_mul' := familyNaturalEnd_product hA }

@[simp] theorem toNaturalEndRingHom_apply (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) :
    toNaturalEndRingHom.{uA, uM} hA x = familyNaturalEnd hA x := rfl

theorem toNaturalEndRingHom_coe (hA : IsIdempotented A) :
    ⇑(toNaturalEndRingHom.{uA, uM} hA) = familyNaturalEnd hA := rfl

@[simp] theorem toNaturalEndRingHom_app (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (M : NondegenerateModuleCat.{uA, uM} A) :
    (toNaturalEndRingHom hA x).app M =
      AddCommGrpCat.ofHom (actionAddHom hA M.property x) := rfl

@[simp] theorem toNaturalEndRingHom_app_hom (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (M : NondegenerateModuleCat.{uA, uM} A) :
    ((toNaturalEndRingHom hA x).app M).hom = actionAddHom hA M.property x := rfl

theorem toNaturalEndRingHom_app_coe (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (M : NondegenerateModuleCat.{uA, uM} A) :
    ⇑((toNaturalEndRingHom hA x).app M).hom =
      IdempotentedRingRightLimitAction.act M.property x := rfl

@[simp] theorem toNaturalEndRingHom_app_apply (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (M : NondegenerateModuleCat.{uA, uM} A)
    (m : M.obj) :
    (toNaturalEndRingHom hA x).app M m =
      IdempotentedRingRightLimitAction.act M.property x m := rfl

theorem toNaturalEndRingHom_app_eq (hA : IsIdempotented A)
    (x : IdempotentedRingRightLimit A) (M : NondegenerateModuleCat.{uA, uM} A)
    (m : M.obj) (e : Idempotent A) (he : (e : A) • m = m) :
    (toNaturalEndRingHom hA x).app M m = x.val e • m :=
  actionAddHom_eq hA M.property x m e he

@[simp] theorem toNaturalEndRingHom_canonical_app_hom (hA : IsIdempotented A)
    (a : A) (M : NondegenerateModuleCat.{uA, uM} A) :
    ((toNaturalEndRingHom hA (canonical a)).app M).hom =
      NonUnitalModule.toEndHom M.obj.isModule a :=
  actionAddHom_canonical hA M.property a

@[simp] theorem toNaturalEndRingHom_canonical_app_apply (hA : IsIdempotented A)
    (a : A) (M : NondegenerateModuleCat.{uA, uM} A) (m : M.obj) :
    (toNaturalEndRingHom hA (canonical a)).app M m = a • m :=
  IdempotentedRingRightLimitAction.canonical_act hA M.property a m

end IdempotentedRingRightLimit
/-! Complete unapplied interfaces with independent scalar and carrier universes. -/

example : (A : Type uA) → [NonUnitalRing A] →
    NonUnitalModuleCat.{uA, uM} A ⥤ AddCommGrpCat.{uM} :=
  @nonUnitalModuleForgetful.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    (nonUnitalModuleForgetful.{uA, uM} A).Additive :=
  @nonUnitalModuleForgetful_additive.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    (M : NonUnitalModuleCat.{uA, uM} A) →
    (nonUnitalModuleForgetful A).obj M = AddCommGrpCat.of M :=
  @nonUnitalModuleForgetful_obj.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    (M : NonUnitalModuleCat.{uA, uM} A) →
    ((nonUnitalModuleForgetful A).obj M : Type uM) = (M : Type uM) :=
  @nonUnitalModuleForgetful_obj_carrier.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{uA, uM} A} → (f : M ⟶ N) →
    (nonUnitalModuleForgetful A).map f = AddCommGrpCat.ofHom f.toAddMonoidHom :=
  @nonUnitalModuleForgetful_map.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{uA, uM} A} → (f : M ⟶ N) →
    ((nonUnitalModuleForgetful A).map f).hom = f.toAddMonoidHom :=
  @nonUnitalModuleForgetful_map_hom.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{uA, uM} A} → (f : M ⟶ N) → (m : M) →
    (nonUnitalModuleForgetful A).map f m = f.toAddMonoidHom m :=
  @nonUnitalModuleForgetful_map_apply.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    NondegenerateModuleCat.{uA, uM} A ⥤ AddCommGrpCat.{uM} :=
  @nondegenerateModuleForgetful.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    (nondegenerateModuleForgetful.{uA, uM} A).Additive :=
  @nondegenerateModuleForgetful_additive.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    nondegenerateModuleForgetful.{uA, uM} A =
      nondegenerateInclusion A ⋙ nonUnitalModuleForgetful A :=
  @nondegenerateModuleForgetful_eq.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    (M : NondegenerateModuleCat.{uA, uM} A) →
    (nondegenerateModuleForgetful A).obj M = AddCommGrpCat.of M.obj :=
  @nondegenerateModuleForgetful_obj.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    (M : NondegenerateModuleCat.{uA, uM} A) →
    ((nondegenerateModuleForgetful A).obj M : Type uM) = (M.obj : Type uM) :=
  @nondegenerateModuleForgetful_obj_carrier.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    {M N : NondegenerateModuleCat.{uA, uM} A} → (f : M ⟶ N) →
    (nondegenerateModuleForgetful A).map f = AddCommGrpCat.ofHom f.hom.toAddMonoidHom :=
  @nondegenerateModuleForgetful_map.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    {M N : NondegenerateModuleCat.{uA, uM} A} → (f : M ⟶ N) →
    ((nondegenerateModuleForgetful A).map f).hom = f.hom.toAddMonoidHom :=
  @nondegenerateModuleForgetful_map_hom.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    {M N : NondegenerateModuleCat.{uA, uM} A} → (f : M ⟶ N) → (m : M.obj) →
    (nondegenerateModuleForgetful A).map f m = f.hom.toAddMonoidHom m :=
  @nondegenerateModuleForgetful_map_apply.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] → Type (max uA (uM + 1)) :=
  @NondegenerateModuleNaturalEnd.{uA, uM}

example (A : Type uA) [NonUnitalRing A] :
    Ring (NondegenerateModuleNaturalEnd.{uA, uM} A) := inferInstance

example : (A : Type uA) → [NonUnitalRing A] →
    Ring (NondegenerateModuleNaturalEnd.{uA, uM} A) :=
  @NondegenerateModuleNaturalEnd.ring.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    (θ η : NondegenerateModuleNaturalEnd.{uA, uM} A) →
    (M : NondegenerateModuleCat.{uA, uM} A) →
    ((θ * η).app M).hom = (θ.app M).hom.comp (η.app M).hom :=
  @NondegenerateModuleNaturalEnd.mul_app_hom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    IdempotentedRingRightLimit A → (M →+ M) :=
  @IdempotentedRingRightLimit.actionAddHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : IdempotentedRingRightLimit A) →
    ⇑(IdempotentedRingRightLimit.actionAddHom hA hM x) =
      IdempotentedRingRightLimitAction.act hM x :=
  @IdempotentedRingRightLimit.actionAddHom_coe.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : IdempotentedRingRightLimit A) → (m : M) → (e : Idempotent A) →
    (e : A) • m = m →
    IdempotentedRingRightLimit.actionAddHom hA hM x m = x.val e • m :=
  @IdempotentedRingRightLimit.actionAddHom_eq.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) → (a : A) →
    IdempotentedRingRightLimit.actionAddHom hA hM (IdempotentedRingRightLimit.canonical a) =
      NonUnitalModule.toEndHom (inferInstance : NonUnitalModule A M) a :=
  @IdempotentedRingRightLimit.actionAddHom_canonical.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    {N : Type uN} → [AddCommGroup N] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) →
    (hM : IsNondegenerate A M) → (hN : IsNondegenerate A N) →
    (f : NonUnitalModuleHom A M N) → (x : IdempotentedRingRightLimit A) →
    f.toAddMonoidHom.comp (IdempotentedRingRightLimit.actionAddHom hA hM x) =
      (IdempotentedRingRightLimit.actionAddHom hA hN x).comp f.toAddMonoidHom :=
  @IdempotentedRingRightLimit.actionAddHom_naturality.{uA, uM, uN}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    IdempotentedRingRightLimit A → NondegenerateModuleNaturalEnd.{uA, uM} A :=
  @IdempotentedRingRightLimit.familyNaturalEnd.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : IdempotentedRingRightLimit A) → (M : NondegenerateModuleCat.{uA, uM} A) →
    ((IdempotentedRingRightLimit.familyNaturalEnd hA x).app M).hom =
      IdempotentedRingRightLimit.actionAddHom hA M.property x :=
  @IdempotentedRingRightLimit.familyNaturalEnd_app_hom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := IdempotentedRingRightLimit.ring hA
    letI := NondegenerateModuleNaturalEnd.ring.{uA, uM} A
    IdempotentedRingRightLimit A →+* NondegenerateModuleNaturalEnd.{uA, uM} A :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    ⇑(IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, uM} hA) =
      IdempotentedRingRightLimit.familyNaturalEnd hA :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_coe.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : IdempotentedRingRightLimit A) → (M : NondegenerateModuleCat.{uA, uM} A) →
    ((IdempotentedRingRightLimit.toNaturalEndRingHom hA x).app M).hom =
      IdempotentedRingRightLimit.actionAddHom hA M.property x :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_app_hom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : IdempotentedRingRightLimit A) → (M : NondegenerateModuleCat.{uA, uM} A) →
    ⇑((IdempotentedRingRightLimit.toNaturalEndRingHom hA x).app M).hom =
      IdempotentedRingRightLimitAction.act M.property x :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_app_coe.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : IdempotentedRingRightLimit A) → (M : NondegenerateModuleCat.{uA, uM} A) →
    (m : M.obj) → (e : Idempotent A) → (e : A) • m = m →
    (IdempotentedRingRightLimit.toNaturalEndRingHom hA x).app M m = x.val e • m :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_app_eq.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (a : A) → (M : NondegenerateModuleCat.{uA, uM} A) →
    ((IdempotentedRingRightLimit.toNaturalEndRingHom hA
      (IdempotentedRingRightLimit.canonical a)).app M).hom =
      NonUnitalModule.toEndHom M.obj.isModule a :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_canonical_app_hom.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (a : A) → (M : NondegenerateModuleCat.{uA, uM} A) → (m : M.obj) →
    (IdempotentedRingRightLimit.toNaturalEndRingHom hA
      (IdempotentedRingRightLimit.canonical a)).app M m = a • m :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_canonical_app_apply.{uA, uM}

/-! Unequal-universe specialization (uA,uM,uN)=(0,1,0). -/

example : (A : Type 0) → [NonUnitalRing A] →
    NonUnitalModuleCat.{0, 1} A ⥤ AddCommGrpCat.{1} :=
  @nonUnitalModuleForgetful.{0, 1}

example : (A : Type 0) → [NonUnitalRing A] →
    (nonUnitalModuleForgetful.{0, 1} A).Additive :=
  @nonUnitalModuleForgetful_additive.{0, 1}

example : (A : Type 0) → [NonUnitalRing A] →
    (M : NonUnitalModuleCat.{0, 1} A) →
    (nonUnitalModuleForgetful A).obj M = AddCommGrpCat.of M :=
  @nonUnitalModuleForgetful_obj.{0, 1}

example : (A : Type 0) → [NonUnitalRing A] →
    (M : NonUnitalModuleCat.{0, 1} A) →
    ((nonUnitalModuleForgetful A).obj M : Type 1) = (M : Type 1) :=
  @nonUnitalModuleForgetful_obj_carrier.{0, 1}

example : (A : Type 0) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{0, 1} A} → (f : M ⟶ N) →
    (nonUnitalModuleForgetful A).map f = AddCommGrpCat.ofHom f.toAddMonoidHom :=
  @nonUnitalModuleForgetful_map.{0, 1}

example : (A : Type 0) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{0, 1} A} → (f : M ⟶ N) →
    ((nonUnitalModuleForgetful A).map f).hom = f.toAddMonoidHom :=
  @nonUnitalModuleForgetful_map_hom.{0, 1}

example : (A : Type 0) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{0, 1} A} → (f : M ⟶ N) → (m : M) →
    (nonUnitalModuleForgetful A).map f m = f.toAddMonoidHom m :=
  @nonUnitalModuleForgetful_map_apply.{0, 1}

example : (A : Type 0) → [NonUnitalRing A] →
    NondegenerateModuleCat.{0, 1} A ⥤ AddCommGrpCat.{1} :=
  @nondegenerateModuleForgetful.{0, 1}

example : (A : Type 0) → [NonUnitalRing A] →
    (nondegenerateModuleForgetful.{0, 1} A).Additive :=
  @nondegenerateModuleForgetful_additive.{0, 1}

example : (A : Type 0) → [NonUnitalRing A] →
    nondegenerateModuleForgetful.{0, 1} A =
      nondegenerateInclusion A ⋙ nonUnitalModuleForgetful A :=
  @nondegenerateModuleForgetful_eq.{0, 1}

example : (A : Type 0) → [NonUnitalRing A] →
    (M : NondegenerateModuleCat.{0, 1} A) →
    (nondegenerateModuleForgetful A).obj M = AddCommGrpCat.of M.obj :=
  @nondegenerateModuleForgetful_obj.{0, 1}

example : (A : Type 0) → [NonUnitalRing A] →
    (M : NondegenerateModuleCat.{0, 1} A) →
    ((nondegenerateModuleForgetful A).obj M : Type 1) = (M.obj : Type 1) :=
  @nondegenerateModuleForgetful_obj_carrier.{0, 1}

example : (A : Type 0) → [NonUnitalRing A] →
    {M N : NondegenerateModuleCat.{0, 1} A} → (f : M ⟶ N) →
    (nondegenerateModuleForgetful A).map f = AddCommGrpCat.ofHom f.hom.toAddMonoidHom :=
  @nondegenerateModuleForgetful_map.{0, 1}

example : (A : Type 0) → [NonUnitalRing A] →
    {M N : NondegenerateModuleCat.{0, 1} A} → (f : M ⟶ N) →
    ((nondegenerateModuleForgetful A).map f).hom = f.hom.toAddMonoidHom :=
  @nondegenerateModuleForgetful_map_hom.{0, 1}

example : (A : Type 0) → [NonUnitalRing A] →
    {M N : NondegenerateModuleCat.{0, 1} A} → (f : M ⟶ N) → (m : M.obj) →
    (nondegenerateModuleForgetful A).map f m = f.hom.toAddMonoidHom m :=
  @nondegenerateModuleForgetful_map_apply.{0, 1}

example : (A : Type 0) → [NonUnitalRing A] → Type (max 0 (1 + 1)) :=
  @NondegenerateModuleNaturalEnd.{0, 1}

example (A : Type 0) [NonUnitalRing A] :
    Ring (NondegenerateModuleNaturalEnd.{0, 1} A) := inferInstance

example : (A : Type 0) → [NonUnitalRing A] →
    Ring (NondegenerateModuleNaturalEnd.{0, 1} A) :=
  @NondegenerateModuleNaturalEnd.ring.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    (θ η : NondegenerateModuleNaturalEnd.{0, 1} A) →
    (M : NondegenerateModuleCat.{0, 1} A) →
    ((θ * η).app M).hom = (θ.app M).hom.comp (η.app M).hom :=
  @NondegenerateModuleNaturalEnd.mul_app_hom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    IdempotentedRingRightLimit A → (M →+ M) :=
  @IdempotentedRingRightLimit.actionAddHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : IdempotentedRingRightLimit A) →
    ⇑(IdempotentedRingRightLimit.actionAddHom hA hM x) =
      IdempotentedRingRightLimitAction.act hM x :=
  @IdempotentedRingRightLimit.actionAddHom_coe.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : IdempotentedRingRightLimit A) → (m : M) → (e : Idempotent A) →
    (e : A) • m = m →
    IdempotentedRingRightLimit.actionAddHom hA hM x m = x.val e • m :=
  @IdempotentedRingRightLimit.actionAddHom_eq.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) → (a : A) →
    IdempotentedRingRightLimit.actionAddHom hA hM (IdempotentedRingRightLimit.canonical a) =
      NonUnitalModule.toEndHom (inferInstance : NonUnitalModule A M) a :=
  @IdempotentedRingRightLimit.actionAddHom_canonical.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    {N : Type 0} → [AddCommGroup N] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) →
    (hM : IsNondegenerate A M) → (hN : IsNondegenerate A N) →
    (f : NonUnitalModuleHom A M N) → (x : IdempotentedRingRightLimit A) →
    f.toAddMonoidHom.comp (IdempotentedRingRightLimit.actionAddHom hA hM x) =
      (IdempotentedRingRightLimit.actionAddHom hA hN x).comp f.toAddMonoidHom :=
  @IdempotentedRingRightLimit.actionAddHom_naturality.{0, 1, 0}

example : {A : Type 0} → [NonUnitalRing A] → IsIdempotented A →
    IdempotentedRingRightLimit A → NondegenerateModuleNaturalEnd.{0, 1} A :=
  @IdempotentedRingRightLimit.familyNaturalEnd.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : IdempotentedRingRightLimit A) → (M : NondegenerateModuleCat.{0, 1} A) →
    ((IdempotentedRingRightLimit.familyNaturalEnd hA x).app M).hom =
      IdempotentedRingRightLimit.actionAddHom hA M.property x :=
  @IdempotentedRingRightLimit.familyNaturalEnd_app_hom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := IdempotentedRingRightLimit.ring hA
    letI := NondegenerateModuleNaturalEnd.ring.{0, 1} A
    IdempotentedRingRightLimit A →+* NondegenerateModuleNaturalEnd.{0, 1} A :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    ⇑(IdempotentedRingRightLimit.toNaturalEndRingHom.{0, 1} hA) =
      IdempotentedRingRightLimit.familyNaturalEnd hA :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_coe.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : IdempotentedRingRightLimit A) → (M : NondegenerateModuleCat.{0, 1} A) →
    ((IdempotentedRingRightLimit.toNaturalEndRingHom hA x).app M).hom =
      IdempotentedRingRightLimit.actionAddHom hA M.property x :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_app_hom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : IdempotentedRingRightLimit A) → (M : NondegenerateModuleCat.{0, 1} A) →
    ⇑((IdempotentedRingRightLimit.toNaturalEndRingHom hA x).app M).hom =
      IdempotentedRingRightLimitAction.act M.property x :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_app_coe.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : IdempotentedRingRightLimit A) → (M : NondegenerateModuleCat.{0, 1} A) →
    (m : M.obj) → (e : Idempotent A) → (e : A) • m = m →
    (IdempotentedRingRightLimit.toNaturalEndRingHom hA x).app M m = x.val e • m :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_app_eq.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (a : A) → (M : NondegenerateModuleCat.{0, 1} A) →
    ((IdempotentedRingRightLimit.toNaturalEndRingHom hA
      (IdempotentedRingRightLimit.canonical a)).app M).hom =
      NonUnitalModule.toEndHom M.obj.isModule a :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_canonical_app_hom.{0, 1}

example : {A : Type 0} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (a : A) → (M : NondegenerateModuleCat.{0, 1} A) → (m : M.obj) →
    (IdempotentedRingRightLimit.toNaturalEndRingHom hA
      (IdempotentedRingRightLimit.canonical a)).app M m = a • m :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_canonical_app_apply.{0, 1}

/-! Unequal-universe specialization (uA,uM,uN)=(1,0,1). -/

example : (A : Type 1) → [NonUnitalRing A] →
    NonUnitalModuleCat.{1, 0} A ⥤ AddCommGrpCat.{0} :=
  @nonUnitalModuleForgetful.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    (nonUnitalModuleForgetful.{1, 0} A).Additive :=
  @nonUnitalModuleForgetful_additive.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    (M : NonUnitalModuleCat.{1, 0} A) →
    (nonUnitalModuleForgetful A).obj M = AddCommGrpCat.of M :=
  @nonUnitalModuleForgetful_obj.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    (M : NonUnitalModuleCat.{1, 0} A) →
    ((nonUnitalModuleForgetful A).obj M : Type 0) = (M : Type 0) :=
  @nonUnitalModuleForgetful_obj_carrier.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{1, 0} A} → (f : M ⟶ N) →
    (nonUnitalModuleForgetful A).map f = AddCommGrpCat.ofHom f.toAddMonoidHom :=
  @nonUnitalModuleForgetful_map.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{1, 0} A} → (f : M ⟶ N) →
    ((nonUnitalModuleForgetful A).map f).hom = f.toAddMonoidHom :=
  @nonUnitalModuleForgetful_map_hom.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    {M N : NonUnitalModuleCat.{1, 0} A} → (f : M ⟶ N) → (m : M) →
    (nonUnitalModuleForgetful A).map f m = f.toAddMonoidHom m :=
  @nonUnitalModuleForgetful_map_apply.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    NondegenerateModuleCat.{1, 0} A ⥤ AddCommGrpCat.{0} :=
  @nondegenerateModuleForgetful.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    (nondegenerateModuleForgetful.{1, 0} A).Additive :=
  @nondegenerateModuleForgetful_additive.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    nondegenerateModuleForgetful.{1, 0} A =
      nondegenerateInclusion A ⋙ nonUnitalModuleForgetful A :=
  @nondegenerateModuleForgetful_eq.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    (M : NondegenerateModuleCat.{1, 0} A) →
    (nondegenerateModuleForgetful A).obj M = AddCommGrpCat.of M.obj :=
  @nondegenerateModuleForgetful_obj.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    (M : NondegenerateModuleCat.{1, 0} A) →
    ((nondegenerateModuleForgetful A).obj M : Type 0) = (M.obj : Type 0) :=
  @nondegenerateModuleForgetful_obj_carrier.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    {M N : NondegenerateModuleCat.{1, 0} A} → (f : M ⟶ N) →
    (nondegenerateModuleForgetful A).map f = AddCommGrpCat.ofHom f.hom.toAddMonoidHom :=
  @nondegenerateModuleForgetful_map.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    {M N : NondegenerateModuleCat.{1, 0} A} → (f : M ⟶ N) →
    ((nondegenerateModuleForgetful A).map f).hom = f.hom.toAddMonoidHom :=
  @nondegenerateModuleForgetful_map_hom.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] →
    {M N : NondegenerateModuleCat.{1, 0} A} → (f : M ⟶ N) → (m : M.obj) →
    (nondegenerateModuleForgetful A).map f m = f.hom.toAddMonoidHom m :=
  @nondegenerateModuleForgetful_map_apply.{1, 0}

example : (A : Type 1) → [NonUnitalRing A] → Type (max 1 (0 + 1)) :=
  @NondegenerateModuleNaturalEnd.{1, 0}

example (A : Type 1) [NonUnitalRing A] :
    Ring (NondegenerateModuleNaturalEnd.{1, 0} A) := inferInstance

example : (A : Type 1) → [NonUnitalRing A] →
    Ring (NondegenerateModuleNaturalEnd.{1, 0} A) :=
  @NondegenerateModuleNaturalEnd.ring.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    (θ η : NondegenerateModuleNaturalEnd.{1, 0} A) →
    (M : NondegenerateModuleCat.{1, 0} A) →
    ((θ * η).app M).hom = (θ.app M).hom.comp (η.app M).hom :=
  @NondegenerateModuleNaturalEnd.mul_app_hom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    IdempotentedRingRightLimit A → (M →+ M) :=
  @IdempotentedRingRightLimit.actionAddHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : IdempotentedRingRightLimit A) →
    ⇑(IdempotentedRingRightLimit.actionAddHom hA hM x) =
      IdempotentedRingRightLimitAction.act hM x :=
  @IdempotentedRingRightLimit.actionAddHom_coe.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) →
    (x : IdempotentedRingRightLimit A) → (m : M) → (e : Idempotent A) →
    (e : A) • m = m →
    IdempotentedRingRightLimit.actionAddHom hA hM x m = x.val e • m :=
  @IdempotentedRingRightLimit.actionAddHom_eq.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    (hA : IsIdempotented A) → (hM : IsNondegenerate A M) → (a : A) →
    IdempotentedRingRightLimit.actionAddHom hA hM (IdempotentedRingRightLimit.canonical a) =
      NonUnitalModule.toEndHom (inferInstance : NonUnitalModule A M) a :=
  @IdempotentedRingRightLimit.actionAddHom_canonical.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] →
    {M : Type 0} → [AddCommGroup M] → [NonUnitalModule A M] →
    {N : Type 1} → [AddCommGroup N] → [NonUnitalModule A N] →
    (hA : IsIdempotented A) →
    (hM : IsNondegenerate A M) → (hN : IsNondegenerate A N) →
    (f : NonUnitalModuleHom A M N) → (x : IdempotentedRingRightLimit A) →
    f.toAddMonoidHom.comp (IdempotentedRingRightLimit.actionAddHom hA hM x) =
      (IdempotentedRingRightLimit.actionAddHom hA hN x).comp f.toAddMonoidHom :=
  @IdempotentedRingRightLimit.actionAddHom_naturality.{1, 0, 1}

example : {A : Type 1} → [NonUnitalRing A] → IsIdempotented A →
    IdempotentedRingRightLimit A → NondegenerateModuleNaturalEnd.{1, 0} A :=
  @IdempotentedRingRightLimit.familyNaturalEnd.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : IdempotentedRingRightLimit A) → (M : NondegenerateModuleCat.{1, 0} A) →
    ((IdempotentedRingRightLimit.familyNaturalEnd hA x).app M).hom =
      IdempotentedRingRightLimit.actionAddHom hA M.property x :=
  @IdempotentedRingRightLimit.familyNaturalEnd_app_hom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    letI := IdempotentedRingRightLimit.ring hA
    letI := NondegenerateModuleNaturalEnd.ring.{1, 0} A
    IdempotentedRingRightLimit A →+* NondegenerateModuleNaturalEnd.{1, 0} A :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    ⇑(IdempotentedRingRightLimit.toNaturalEndRingHom.{1, 0} hA) =
      IdempotentedRingRightLimit.familyNaturalEnd hA :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_coe.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : IdempotentedRingRightLimit A) → (M : NondegenerateModuleCat.{1, 0} A) →
    ((IdempotentedRingRightLimit.toNaturalEndRingHom hA x).app M).hom =
      IdempotentedRingRightLimit.actionAddHom hA M.property x :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_app_hom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : IdempotentedRingRightLimit A) → (M : NondegenerateModuleCat.{1, 0} A) →
    ⇑((IdempotentedRingRightLimit.toNaturalEndRingHom hA x).app M).hom =
      IdempotentedRingRightLimitAction.act M.property x :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_app_coe.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (x : IdempotentedRingRightLimit A) → (M : NondegenerateModuleCat.{1, 0} A) →
    (m : M.obj) → (e : Idempotent A) → (e : A) • m = m →
    (IdempotentedRingRightLimit.toNaturalEndRingHom hA x).app M m = x.val e • m :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_app_eq.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (a : A) → (M : NondegenerateModuleCat.{1, 0} A) →
    ((IdempotentedRingRightLimit.toNaturalEndRingHom hA
      (IdempotentedRingRightLimit.canonical a)).app M).hom =
      NonUnitalModule.toEndHom M.obj.isModule a :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_canonical_app_hom.{1, 0}

example : {A : Type 1} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (a : A) → (M : NondegenerateModuleCat.{1, 0} A) → (m : M.obj) →
    (IdempotentedRingRightLimit.toNaturalEndRingHom hA
      (IdempotentedRingRightLimit.canonical a)).app M m = a • m :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_canonical_app_apply.{1, 0}

/-! Competing choices cannot replace the actual source and target rings. -/
section CompetingRings

variable {A : Type uA} [NonUnitalRing A]
  [competingFamilyRing : Ring (IdempotentedRingRightLimit A)]
  [competingNaturalEndRing : Ring (NondegenerateModuleNaturalEnd.{uA, uM} A)]

example : (hA : IsIdempotented A) →
    letI := IdempotentedRingRightLimit.ring hA
    letI := NondegenerateModuleNaturalEnd.ring.{uA, uM} A
    IdempotentedRingRightLimit A →+* NondegenerateModuleNaturalEnd.{uA, uM} A :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, uM} A _

example : (hA : IsIdempotented A) →
    ⇑(IdempotentedRingRightLimit.toNaturalEndRingHom.{uA, uM} hA) =
      IdempotentedRingRightLimit.familyNaturalEnd hA :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_coe.{uA, uM} A _

example : (hA : IsIdempotented A) → (x : IdempotentedRingRightLimit A) →
    (M : NondegenerateModuleCat.{uA, uM} A) →
    ((IdempotentedRingRightLimit.toNaturalEndRingHom hA x).app M).hom =
      IdempotentedRingRightLimit.actionAddHom hA M.property x :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_app_hom.{uA, uM} A _

example : (hA : IsIdempotented A) → (x : IdempotentedRingRightLimit A) →
    (M : NondegenerateModuleCat.{uA, uM} A) →
    (m : M.obj) → (e : Idempotent A) → (e : A) • m = m →
    (IdempotentedRingRightLimit.toNaturalEndRingHom hA x).app M m = x.val e • m :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_app_eq.{uA, uM} A _

example : (hA : IsIdempotented A) → (a : A) →
    (M : NondegenerateModuleCat.{uA, uM} A) →
    ((IdempotentedRingRightLimit.toNaturalEndRingHom hA
      (IdempotentedRingRightLimit.canonical a)).app M).hom =
      NonUnitalModule.toEndHom M.obj.isModule a :=
  @IdempotentedRingRightLimit.toNaturalEndRingHom_canonical_app_hom.{uA, uM} A _

end CompetingRings

/-! Explicit original actions survive a competing action on the very same carrier. -/
section CompetingActions

variable {A : Type uA} [NonUnitalRing A] {M : Type uM} [AddCommGroup M]
  (originalAction : NonUnitalModule A M) [competingAction : NonUnitalModule A M]

example : (hA : IsIdempotented A) →
    (hM : @IsNondegenerate A M _ _ originalAction) → (x : IdempotentedRingRightLimit A) →
    ⇑(@IdempotentedRingRightLimit.actionAddHom A _ M _ originalAction hA hM x) =
      @IdempotentedRingRightLimitAction.act A _ M _ originalAction hM x :=
  @IdempotentedRingRightLimit.actionAddHom_coe A _ M _ originalAction

example : (hA : IsIdempotented A) →
    (hM : @IsNondegenerate A M _ _ originalAction) → (x : IdempotentedRingRightLimit A) →
    (m : M) → (e : Idempotent A) →
    @SMul.smul A M originalAction.toDistribSMul.toSMul (e : A) m = m →
    @IdempotentedRingRightLimit.actionAddHom A _ M _ originalAction hA hM x m =
      @SMul.smul A M originalAction.toDistribSMul.toSMul (x.val e) m :=
  @IdempotentedRingRightLimit.actionAddHom_eq A _ M _ originalAction

example : (hA : IsIdempotented A) →
    (hM : @IsNondegenerate A M _ _ originalAction) → (a : A) →
    @IdempotentedRingRightLimit.actionAddHom A _ M _ originalAction hA hM
      (IdempotentedRingRightLimit.canonical a) = NonUnitalModule.toEndHom originalAction a :=
  @IdempotentedRingRightLimit.actionAddHom_canonical A _ M _ originalAction

example (hA : IsIdempotented A) (hM : @IsNondegenerate A M _ _ originalAction)
    (x : IdempotentedRingRightLimit A) :
    ((IdempotentedRingRightLimit.toNaturalEndRingHom hA x).app
      ⟨@NonUnitalModuleCat.of A _ M _ originalAction, hM⟩).hom =
      @IdempotentedRingRightLimit.actionAddHom A _ M _ originalAction hA hM x := rfl

example (f : @NonUnitalModuleHom A M M _ _ _ originalAction competingAction) :
    ((nonUnitalModuleForgetful A).map (show
      @NonUnitalModuleCat.of A _ M _ originalAction ⟶
        @NonUnitalModuleCat.of A _ M _ competingAction from f)).hom =
      @NonUnitalModuleHom.toAddMonoidHom A M M _ _ _
        originalAction competingAction f := rfl

end CompetingActions

/-! The scalar carrier itself can carry an original zero action. -/
example {A : Type uA} [NonUnitalRing A] :
    letI := NonUnitalModule.zero (A := A) (M := A)
    ((nonUnitalModuleForgetful A).obj (NonUnitalModuleCat.of A A) : Type uA) = A := rfl

/-! Zero groups, including zero-ring actions, satisfy every interface. -/
section ZeroGroups

variable {A : Type uA} [NonUnitalRing A] {M : Type uM}
  [AddCommGroup M] [NonUnitalModule A M] [Subsingleton M]

example (hA : IsIdempotented A) :
    ∃ hM : IsNondegenerate A M, ∀ x : IdempotentedRingRightLimit A,
      IdempotentedRingRightLimit.actionAddHom hA hM x = 0 := by
  have hM : IsNondegenerate A M := by
    intro m
    exact ⟨⟨0, zero_mul 0⟩, Subsingleton.elim _ _⟩
  refine ⟨hM, ?_⟩
  intro x
  apply AddMonoidHom.ext
  intro m
  exact Subsingleton.elim _ _

example (hA : IsIdempotented A) (hM : IsNondegenerate A M)
    (x : IdempotentedRingRightLimit A) :
    ((IdempotentedRingRightLimit.toNaturalEndRingHom hA x).app
      ⟨NonUnitalModuleCat.of A M, hM⟩).hom = 0 := by
  change IdempotentedRingRightLimit.actionAddHom hA hM x = 0
  apply AddMonoidHom.ext
  intro m
  exact Subsingleton.elim _ _

end ZeroGroups

section ZeroRing

variable {A : Type uA} [NonUnitalRing A] [Subsingleton A]

example : ∃ hA : IsIdempotented A,
    ∀ (x : IdempotentedRingRightLimit A) (M : NondegenerateModuleCat.{uA, uM} A),
      ((IdempotentedRingRightLimit.toNaturalEndRingHom hA x).app M).hom = 0 := by
  have hA : IsIdempotented A := by
    intro s
    refine ⟨⟨0, zero_mul 0⟩, ?_⟩
    intro a _ha
    exact Subsingleton.elim _ _
  refine ⟨hA, ?_⟩
  intro x M
  apply AddMonoidHom.ext
  intro m
  obtain ⟨e, he⟩ := M.property m
  change IdempotentedRingRightLimitAction.act M.property x m = 0
  rw [IdempotentedRingRightLimitAction.act_eq hA M.property x m e he]
  have hx : x.val e = 0 := Subsingleton.elim _ _
  rw [hx]
  exact @NonUnitalModule.zero_smul A M.obj _ _ M.obj.isModule m

end ZeroRing

end Langlands.Algebra
