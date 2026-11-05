import Langlands.Algebra.RenardAlgebraActionLocalization
import Mathlib.Algebra.Module.ULift
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The category of compatible algebra actions and the localized structured arrow

Construction content for the categorical form of the last sentence of Renard A.III.1,
example 5 (9 July 2026, printed p. 252 / PDF p. 258). The algebra and its actions may be
nonunital. Universality of the canonical structured arrow is a separate successor.
-/

set_option autoImplicit false

universe u v w x y z

noncomputable section

namespace Langlands.Renard.AlgebraActionLocalization

open CategoryTheory Langlands.Algebra EndomorphismLocalization

/-- `k`-modules carrying a compatible, possibly nonunital, action of `B`. -/
structure ActionModuleCat (k : Type u) [CommRing k] (B : Type v) [NonUnitalRing B]
    [Module k B] : Type (max u v (w + 1)) where
  /-- The underlying `k`-module. -/
  carrier : Type w
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module k carrier]
  /-- The specified action of `B` by `k`-linear endomorphisms. -/
  action : B →ₙₐ[k] Module.End k carrier

attribute [instance] ActionModuleCat.isAddCommGroup ActionModuleCat.isModule

namespace ActionModuleCat

variable {k : Type u} [CommRing k] {B : Type v} [NonUnitalRing B] [Module k B]

instance : CoeSort (ActionModuleCat.{u, v, w} k B) (Type w) := ⟨ActionModuleCat.carrier⟩

/-- Bundle an actual module with an actual action. -/
abbrev of (M : Type w) [AddCommGroup M] [Module k M] (ρ : B →ₙₐ[k] Module.End k M) :
    ActionModuleCat.{u, v, w} k B :=
  ⟨M, ρ⟩

/-- Morphisms are exactly the actual linear intertwiners of the two actions. -/
structure Hom (M N : ActionModuleCat.{u, v, w} k B) where
  /-- The underlying linear intertwiner. -/
  hom : LinearIntertwiner M.action N.action

instance : Category (ActionModuleCat.{u, v, w} k B) where
  Hom := Hom
  id M := ⟨LinearIntertwiner.id M.action⟩
  comp f g := ⟨g.hom.comp f.hom⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Bundle an actual linear intertwiner as a morphism. -/
abbrev ofHom {M N : ActionModuleCat.{u, v, w} k B} (f : LinearIntertwiner M.action N.action) :
    M ⟶ N :=
  ⟨f⟩

@[simp] theorem hom_ofHom {M N : ActionModuleCat.{u, v, w} k B}
    (f : LinearIntertwiner M.action N.action) : (ofHom f).hom = f := rfl

@[simp] theorem hom_id (M : ActionModuleCat.{u, v, w} k B) :
    (𝟙 M : M ⟶ M).hom = LinearIntertwiner.id M.action := rfl

@[simp] theorem hom_comp {M N P : ActionModuleCat.{u, v, w} k B} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

@[ext] theorem hom_ext {M N : ActionModuleCat.{u, v, w} k B} {f g : M ⟶ N}
    (h : ∀ z, f.hom z = g.hom z) : f = g := by
  cases f
  cases g
  exact congrArg Hom.mk (LinearIntertwiner.ext h)

/-- Categorical morphisms are in bijection with the actual linear intertwiners. -/
def homEquiv (M N : ActionModuleCat.{u, v, w} k B) :
    (M ⟶ N) ≃ LinearIntertwiner M.action N.action where
  toFun f := f.hom
  invFun f := ofHom f
  left_inv _ := rfl
  right_inv _ := rfl

end ActionModuleCat

section Category

variable (k : Type u) [CommRing k] (B : Type v) [NonUnitalRing B] [Module k B]

/-- Modules with a compatible action and a specified endomorphism commuting with it;
morphisms are the linear intertwiners of both structures. -/
abbrev ActionEndomorphismCat :=
  Endofunctor.Algebra (𝟭 (ActionModuleCat.{u, v, w} k B))

variable {k B}

/-- The specified endomorphism as an ordinary linear endomorphism. -/
abbrev endomorphism (A : ActionEndomorphismCat.{u, v, w} k B) : Module.End k A.a :=
  A.str.hom.toLinearMap

/-- The specified endomorphism commutes with the action. -/
theorem endomorphism_action (A : ActionEndomorphismCat.{u, v, w} k B) (b : B) (z : A.a) :
    endomorphism A (A.a.action b z) = A.a.action b (endomorphism A z) :=
  A.str.hom.map_action b z

/-- The categorical compatibility equation is the ordinary intertwining equation. -/
theorem intertwining_iff (A A' : ActionEndomorphismCat.{u, v, w} k B) (f : A.a ⟶ A'.a) :
    ((𝟭 (ActionModuleCat.{u, v, w} k B)).map f ≫ A'.str = A.str ≫ f) ↔
      ∀ z : A.a, f.hom (endomorphism A z) = endomorphism A' (f.hom z) := by
  constructor
  · intro h z
    exact (congrArg (fun g : A.a ⟶ A'.a => g.hom z) h).symm
  · intro h
    ext z
    exact (h z).symm

/-- Morphisms correspond exactly to linear intertwiners of the actions that also
intertwine the specified endomorphisms. -/
def homEquiv (A A' : ActionEndomorphismCat.{u, v, w} k B) :
    (A ⟶ A') ≃ {f : LinearIntertwiner A.a.action A'.a.action //
      ∀ z, f (endomorphism A z) = endomorphism A' (f z)} where
  toFun f := ⟨f.f.hom, (intertwining_iff A A' f.f).mp f.h⟩
  invFun f :=
    { f := ActionModuleCat.ofHom f.1
      h := (intertwining_iff A A' (ActionModuleCat.ofHom f.1)).mpr f.2 }
  left_inv _ := rfl
  right_inv _ := rfl

variable (k B)

/-- Invertibility of the specified endomorphism, as a property of actual objects. -/
def invertibleActionProperty : ObjectProperty (ActionEndomorphismCat.{u, v, w} k B) :=
  fun A => IsUnit (endomorphism A)

/-- The full subcategory retaining every intertwiner between objects whose specified
endomorphism is invertible. -/
abbrev InvertibleActionEndomorphismCat :=
  (invertibleActionProperty.{u, v, w} k B).FullSubcategory

/-- Inclusion of the invertible objects. -/
abbrev invertibleActionInclusion :
    InvertibleActionEndomorphismCat.{u, v, w} k B ⥤ ActionEndomorphismCat.{u, v, w} k B :=
  (invertibleActionProperty.{u, v, w} k B).ι

/-- The inclusion is fully faithful, with no restriction on intertwiners. -/
abbrev invertibleActionInclusionFullyFaithful :
    (invertibleActionInclusion.{u, v, w} k B).FullyFaithful :=
  (invertibleActionProperty.{u, v, w} k B).fullyFaithfulι

end Category

section Lift

variable {k : Type u} [CommRing k] {B : Type v} [NonUnitalRing B] [Module k B]
  {V : Type w} [AddCommGroup V] [Module k V] {W : Type y} [AddCommGroup W] [Module k W]

/-- Conjugate an action through the native `k`-linear `ULift` equivalence. -/
def liftAction (ρ : B →ₙₐ[k] Module.End k V) : B →ₙₐ[k] Module.End k (ULift.{x} V) where
  toFun b := (ULift.moduleEquiv (R := k)).symm.toLinearMap ∘ₗ ρ b ∘ₗ
    (ULift.moduleEquiv (R := k)).toLinearMap
  map_smul' c b := by
    ext z
    change ρ (c • b) z.down = c • ρ b z.down
    rw [map_smul, LinearMap.smul_apply]
  map_zero' := by
    ext z
    change ρ 0 z.down = 0
    rw [map_zero, LinearMap.zero_apply]
  map_add' b c := by
    ext z
    change ρ (b + c) z.down = ρ b z.down + ρ c z.down
    rw [map_add, LinearMap.add_apply]
  map_mul' b c := by
    ext z
    change ρ (b * c) z.down = ρ b (ρ c z.down)
    rw [map_mul, Module.End.mul_apply]

@[simp] theorem liftAction_up (ρ : B →ₙₐ[k] Module.End k V) (b : B) (z : V) :
    liftAction.{u, v, w, x} ρ b (ULift.up z) = ULift.up (ρ b z) := rfl

@[simp] theorem liftAction_down (ρ : B →ₙₐ[k] Module.End k V) (b : B) (z : ULift.{x} V) :
    (liftAction.{u, v, w, x} ρ b z).down = ρ b z.down := rfl

/-- Conjugate a linear intertwiner through the native lifts, with independent lift
universes on source and target. -/
def liftIntertwiner {ρ : B →ₙₐ[k] Module.End k V} {σ : B →ₙₐ[k] Module.End k W}
    (f : LinearIntertwiner ρ σ) :
    LinearIntertwiner (liftAction.{u, v, w, x} ρ) (liftAction.{u, v, y, z} σ) where
  toLinearMap := (ULift.moduleEquiv (R := k)).symm.toLinearMap ∘ₗ f.toLinearMap ∘ₗ
    (ULift.moduleEquiv (R := k)).toLinearMap
  map_action' b z := congrArg ULift.up (f.map_action b z.down)

@[simp] theorem liftIntertwiner_up {ρ : B →ₙₐ[k] Module.End k V}
    {σ : B →ₙₐ[k] Module.End k W} (f : LinearIntertwiner ρ σ) (z : V) :
    liftIntertwiner.{u, v, w, x, y, z} f (ULift.up z) = ULift.up (f z) := rfl

@[simp] theorem liftIntertwiner_down {ρ : B →ₙₐ[k] Module.End k V}
    {σ : B →ₙₐ[k] Module.End k W} (f : LinearIntertwiner ρ σ) (z : ULift.{x} V) :
    (liftIntertwiner.{u, v, w, x, y, z} f z).down = f z.down := rfl

end Lift

section Localization

variable (k : Type u) [CommRing k] (B : Type v) [NonUnitalRing B] [Module k B]

/-- Raise the module, its action and its endomorphism through the native lifts, so that
the source and every localized target share the carrier universe `max u w x`. -/
def raisedFunctor :
    ActionEndomorphismCat.{u, v, w} k B ⥤ ActionEndomorphismCat.{u, v, max u w x} k B where
  obj A :=
    { a := ActionModuleCat.of (ULift.{max u x} A.a) (liftAction A.a.action)
      str := ActionModuleCat.ofHom (liftIntertwiner A.str.hom) }
  map {A A'} f :=
    { f := ActionModuleCat.ofHom (liftIntertwiner f.f.hom)
      h := by
        ext z
        exact ((intertwining_iff A A' f.f).mp f.h z.down).symm }
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem raisedFunctor_action_up (A : ActionEndomorphismCat.{u, v, w} k B) (b : B)
    (z : A.a) :
    ((raisedFunctor.{u, v, w, x} k B).obj A).a.action b (ULift.up z) =
      ULift.up (A.a.action b z) := rfl

@[simp] theorem raisedFunctor_endomorphism_up (A : ActionEndomorphismCat.{u, v, w} k B)
    (z : A.a) :
    endomorphism ((raisedFunctor.{u, v, w, x} k B).obj A) (ULift.up z) =
      ULift.up (endomorphism A z) := rfl

@[simp] theorem raisedFunctor_map_up {A A' : ActionEndomorphismCat.{u, v, w} k B}
    (f : A ⟶ A') (z : A.a) :
    ((raisedFunctor.{u, v, w, x} k B).map f).f.hom (ULift.up z) = ULift.up (f.f.hom z) := rfl

variable {k B}

/-- The published localized action at an actual object. -/
abbrev objectLocalizedAction (A : ActionEndomorphismCat.{u, v, w} k B) :
    B →ₙₐ[k] Module.End k (Localized (endomorphism A)) :=
  localizedAction (endomorphism A) A.a.action (endomorphism_action A)

/-- The localized object: the published localization carrier, action and localized
operator, lifted to the common carrier universe `max u w x`. -/
def localizedObject (A : ActionEndomorphismCat.{u, v, w} k B) :
    InvertibleActionEndomorphismCat.{u, v, max u w x} k B :=
  ⟨{ a := ActionModuleCat.of (ULift.{x} (Localized (endomorphism A)))
        (liftAction (objectLocalizedAction A))
     str := ActionModuleCat.ofHom (liftIntertwiner
        (localizedEndIntertwiner (endomorphism A) A.a.action (endomorphism_action A))) }, by
    change IsUnit ((ULift.moduleEquiv (R := k)).symm.toLinearMap ∘ₗ
      localizedEnd (endomorphism A) ∘ₗ (ULift.moduleEquiv (R := k)).toLinearMap)
    rw [Module.End.isUnit_iff]
    exact (ULift.moduleEquiv (R := k)).symm.bijective.comp
      ((localizedEquiv (endomorphism A)).bijective.comp
        (ULift.moduleEquiv (R := k)).bijective)⟩

@[simp] theorem localizedObject_action_up (A : ActionEndomorphismCat.{u, v, w} k B) (b : B)
    (z : Localized (endomorphism A)) :
    (localizedObject.{u, v, w, x} A).obj.a.action b (ULift.up z) =
      ULift.up (objectLocalizedAction A b z) := rfl

@[simp] theorem localizedObject_endomorphism_up (A : ActionEndomorphismCat.{u, v, w} k B)
    (z : Localized (endomorphism A)) :
    endomorphism (localizedObject.{u, v, w, x} A).obj (ULift.up z) =
      ULift.up (localizedEnd (endomorphism A) z) := rfl

/-- The actual canonical map iota, lifted, as a morphism from the raised object to the
localized object. -/
def canonicalArrow (A : ActionEndomorphismCat.{u, v, w} k B) :
    (raisedFunctor.{u, v, w, x} k B).obj A ⟶
      (invertibleActionInclusion k B).obj (localizedObject.{u, v, w, x} A) where
  f := ActionModuleCat.ofHom
    (liftIntertwiner (iotaIntertwiner (endomorphism A) A.a.action (endomorphism_action A)))
  h := by
    ext z
    exact congrArg ULift.up (iota_intertwines (endomorphism A) z.down).symm

@[simp] theorem canonicalArrow_up (A : ActionEndomorphismCat.{u, v, w} k B) (z : A.a) :
    (canonicalArrow.{u, v, w, x} A).f.hom (ULift.up z) =
      ULift.up (iota (endomorphism A) z) := rfl

/-- The canonical structured arrow from the raised object to the inclusion of invertible
objects. -/
def canonicalStructuredArrow (A : ActionEndomorphismCat.{u, v, w} k B) :
    StructuredArrow ((raisedFunctor.{u, v, w, x} k B).obj A)
      (invertibleActionInclusion.{u, v, max u w x} k B) :=
  StructuredArrow.mk (canonicalArrow.{u, v, w, x} A)

@[simp] theorem canonicalStructuredArrow_right (A : ActionEndomorphismCat.{u, v, w} k B) :
    (canonicalStructuredArrow.{u, v, w, x} A).right = localizedObject.{u, v, w, x} A := rfl

@[simp] theorem canonicalStructuredArrow_hom (A : ActionEndomorphismCat.{u, v, w} k B) :
    (canonicalStructuredArrow.{u, v, w, x} A).hom = canonicalArrow.{u, v, w, x} A := rfl

end Localization

end Langlands.Renard.AlgebraActionLocalization
