import Langlands.Geometry.FormalGroup.RationalBaseChange

/-! # Actions of coefficient orders on formal modules -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw

variable {O : Type u} [CommRing O]
variable {A : Type v} [Ring A] [Algebra O A]
variable {R : Type w} [CommRing R] [Algebra O R]
variable {S : Type z} [CommRing S] [Algebra O S]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]

namespace Hom

/-- Coefficient extension on the ring of O-linear formal endomorphisms. -/
def mapEnd (M : ModuleLaw O R σ) (φ : R →ₐ[O] S) :
    Hom M M →+* Hom (M.map φ) (M.map φ) where
  toFun f := f.map φ
  map_zero' := (mapLinear φ).map_zero
  map_add' := (mapLinear φ).map_add
  map_one' := map_id φ
  map_mul' := map_comp φ

end Hom

/-- An action of a possibly noncommutative O-algebra by actual O-linear formal
endomorphisms, restricting to the given action of O. -/
structure OrderAction (A : Type v) [Ring A] [Algebra O A] (M : ModuleLaw O R σ) where
  action : A →+* Hom M M
  extends_scalars : ∀ a : O, (action (algebraMap O A a)).toHom = M.action a

namespace OrderAction

variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}
variable (E : OrderAction A M) (E' : OrderAction A N) (E'' : OrderAction A P)

/-- Extend coefficients of the endomorphisms supplying the order action. -/
def map (φ : R →ₐ[O] S) : OrderAction A (M.map φ) where
  action := (Hom.mapEnd M φ).comp E.action
  extends_scalars a := by
    change ((E.action (algebraMap O A a)).toHom.map φ.toRingHom) =
      (M.action a).map φ.toRingHom
    rw [E.extends_scalars]

/-- Twist an order action by an O-algebra automorphism of the order. -/
def twist (α : A ≃ₐ[O] A) : OrderAction A M where
  action := E.action.comp α.toAlgHom.toRingHom
  extends_scalars a := by
    change (E.action (α (algebraMap O A a))).toHom = M.action a
    rw [α.commutes, E.extends_scalars]

@[simp]
theorem map_action (φ : R →ₐ[O] S) (a : A) :
    (E.map φ).action a = (E.action a).map φ := rfl

@[simp]
theorem twist_action (α : A ≃ₐ[O] A) (a : A) :
    (E.twist α).action a = E.action (α a) := rfl

/-- Points indexed by the order action, with their induced A-module structure. -/
@[nolint unusedArguments]
def Point (_E : OrderAction A M) (κ : Type) := M.Point κ

instance (κ : Type) : AddCommGroup (E.Point κ) :=
  inferInstanceAs (AddCommGroup (M.Point κ))

instance (κ : Type) : SMul A (E.Point κ) :=
  ⟨fun a x => (E.action a).onPoints x⟩

instance (κ : Type) : Module A (E.Point κ) where
  one_smul x := by
    change (E.action 1).onPoints x = x
    rw [_root_.map_one]
    exact Hom.onPoints_id x
  mul_smul a b x := by
    change (E.action (a * b)).onPoints x =
      (E.action a).onPoints ((E.action b).onPoints x)
    rw [_root_.map_mul]
    exact Hom.onPoints_comp _ _ x
  smul_zero a := (E.action a).onPoints.map_zero
  smul_add a x y := (E.action a).onPoints.map_add x y
  add_smul a b x := by
    change (E.action (a + b)).onPoints x =
      (E.action a).onPoints x + (E.action b).onPoints x
    rw [_root_.map_add]
    exact Hom.onPoints_add _ _ x
  zero_smul x := by
    change (E.action 0).onPoints x = 0
    rw [_root_.map_zero]
    exact Hom.onPoints_zero x

@[simp]
theorem smul_point {κ : Type} (a : A) (x : E.Point κ) :
    a • x = (E.action a).onPoints x := rfl

/-- Restriction of the evaluated A-action is the original O-action. -/
theorem scalar_point {κ : Type} (a : O) (x : E.Point κ) :
    (algebraMap O A a) • x = (M.action a).onPoints x := by
  change (E.action (algebraMap O A a)).toHom.onPoints x = _
  rw [E.extends_scalars]

/-- Coefficient extension is linear for the full order action. -/
def mapPoints {κ : Type} (φ : R →ₐ[O] S) : E.Point κ →ₗ[A] (E.map φ).Point κ where
  toFun := M.mapPoints φ
  map_add' := (M.mapPoints φ).map_add
  map_smul' a x := by
    change SeriesPoint R σ κ at x
    change (SeriesPoint.eval (E.action a).toHom.toCoordinateMap x).map φ.toRingHom =
      SeriesPoint.eval ((E.action a).toHom.toCoordinateMap.map φ.toRingHom)
        (x.map φ.toRingHom)
    exact SeriesPoint.map_eval _ _ _

/-- The actual O-submodule of formal homomorphisms commuting with the order. -/
def homSubmodule : Submodule O (ModuleLaw.Hom M N) where
  carrier := {f | ∀ a : A, f.comp (E.action a) = (E'.action a).comp f}
  zero_mem' := by intro a; simp
  add_mem' := by
    intro f g hf hg a
    simp only [Hom.add_comp, Hom.comp_add, hf a, hg a]
  smul_mem' := by
    intro a f hf b
    simp only [Hom.smul_comp, Hom.comp_smul, hf b]

/-- Order-linear formal homomorphisms, as a submodule of actual formal Hom. -/
def Hom : Type _ := ↥(E.homSubmodule E')

instance : AddCommGroup (Hom E E') :=
  inferInstanceAs (AddCommGroup ↥(E.homSubmodule E'))

instance : Module O (Hom E E') :=
  inferInstanceAs (Module O ↥(E.homSubmodule E'))

namespace Hom

variable {E E' E''}

/-- The underlying formal map commutes with every order endomorphism. -/
theorem commutes (f : Hom E E') (a : A) :
    f.val.comp (E.action a) = (E'.action a).comp f.val := f.property a

/-- Identity order-linear formal map. -/
def id (E : OrderAction A M) : Hom E E :=
  ⟨ModuleLaw.Hom.id M, by intro a; simp⟩

/-- Compose order-linear formal maps. -/
def comp (g : Hom E' E'') (f : Hom E E') : Hom E E'' :=
  ⟨g.val.comp f.val, by
    intro a
    rw [ModuleLaw.Hom.comp_assoc, f.commutes,
      ← ModuleLaw.Hom.comp_assoc, g.commutes, ModuleLaw.Hom.comp_assoc]⟩

/-- Order-linear formal maps evaluate to A-linear maps on points. -/
def onPoints {κ : Type} (f : Hom E E') : E.Point κ →ₗ[A] E'.Point κ where
  toFun := f.val.onPoints
  map_add' := f.val.onPoints.map_add
  map_smul' a x := by
    change M.Point κ at x
    change f.val.onPoints ((E.action a).onPoints x) =
      (E'.action a).onPoints (f.val.onPoints x)
    have h := congrArg (fun h : ModuleLaw.Hom M N => h.onPoints x) (f.commutes a)
    simpa only [ModuleLaw.Hom.onPoints_comp] using h

@[simp]
theorem onPoints_id {κ : Type} (x : E.Point κ) : (id E).onPoints x = x :=
  ModuleLaw.Hom.onPoints_id x

@[simp]
theorem onPoints_comp {κ : Type} (g : Hom E' E'') (f : Hom E E') (x : E.Point κ) :
    (g.comp f).onPoints x = g.onPoints (f.onPoints x) :=
  ModuleLaw.Hom.onPoints_comp _ _ x

/-- Extend coefficients of an order-linear formal map. -/
def map (f : Hom E E') (φ : R →ₐ[O] S) : Hom (E.map φ) (E'.map φ) :=
  ⟨f.val.map φ, by
    intro a
    change (f.val.map φ).comp ((E.action a).map φ) =
      ((E'.action a).map φ).comp (f.val.map φ)
    rw [← ModuleLaw.Hom.map_comp, f.commutes, ModuleLaw.Hom.map_comp]⟩

@[simp]
theorem map_id (φ : R →ₐ[O] S) : (id E).map φ = id (E.map φ) := by
  apply Subtype.ext
  exact ModuleLaw.Hom.map_id φ

@[simp]
theorem map_comp (φ : R →ₐ[O] S) (g : Hom E' E'') (f : Hom E E') :
    (g.comp f).map φ = (g.map φ).comp (f.map φ) := by
  apply Subtype.ext
  exact ModuleLaw.Hom.map_comp φ g.val f.val

end Hom

/-- An order-linear isomorphism consists of inverse actual order-linear maps. -/
structure Iso where
  hom : Hom E E'
  inv : Hom E' E
  inv_hom : inv.comp hom = Hom.id E
  hom_inv : hom.comp inv = Hom.id E'

namespace Iso

variable {E E'}

/-- Forget the extra order action from an isomorphism. -/
def toModuleIso (f : Iso E E') : ModuleLaw.Iso M N where
  hom := f.hom.val
  inv := f.inv.val
  inv_hom := congrArg Subtype.val f.inv_hom
  hom_inv := congrArg Subtype.val f.hom_inv

/-- An order-linear isomorphism gives an A-linear equivalence on points. -/
def onPoints {κ : Type} (f : Iso E E') : E.Point κ ≃ₗ[A] E'.Point κ where
  toFun := f.hom.onPoints
  invFun := f.inv.onPoints
  map_add' := f.hom.onPoints.map_add
  map_smul' := f.hom.onPoints.map_smul
  left_inv x := by rw [← Hom.onPoints_comp, f.inv_hom, Hom.onPoints_id]
  right_inv x := by rw [← Hom.onPoints_comp, f.hom_inv, Hom.onPoints_id]

/-- Coefficient extension preserves order-linear isomorphisms. -/
def map (f : Iso E E') (φ : R →ₐ[O] S) : Iso (E.map φ) (E'.map φ) where
  hom := f.hom.map φ
  inv := f.inv.map φ
  inv_hom := by rw [← Hom.map_comp, f.inv_hom, Hom.map_id]
  hom_inv := by rw [← Hom.map_comp, f.hom_inv, Hom.map_id]

end Iso

end OrderAction

end Langlands.FormalGroup.ModuleLaw
