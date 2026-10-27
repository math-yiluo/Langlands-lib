import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Renard's Hom functors to integer and endomorphism modules

Renard A.VIII.2 defines `Hom_A(P, •)` and `Hom_A(•, P)` with values in `ℤ-mod`.
They are Mathlib's actual endomorphism-module-valued Hom functors with scalars restricted
along the integer casts `ℤ → (End P)ᵐᵒᵖ` and `ℤ → End P`. See the paired Markdown for the
source correspondence and the action conventions.
-/

noncomputable section

open CategoryTheory Opposite

namespace Langlands.CategoryTheory.Renard

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

section Covariant

/-- Renard's covariant `Hom_A(P, •) : A → ℤ-mod`: the right `End P`-module functor
`preadditiveCoyonedaObj P` with scalars restricted along `ℤ → (End P)ᵐᵒᵖ`. -/
abbrev preadditiveCoyonedaInt (P : C) : C ⥤ ModuleCat.{v} ℤ :=
  preadditiveCoyonedaObj P ⋙ ModuleCat.restrictScalars (Int.castRingHom (End P)ᵐᵒᵖ)

variable (P : C)

/-- The carrier of `Hom_A(P, X)` is the Hom type `P ⟶ X`. -/
theorem preadditiveCoyonedaInt_obj_carrier (X : C) :
    ((preadditiveCoyonedaInt P).obj X : Type v) = (P ⟶ X) := rfl

/-- The covariant Hom map sends `f : P ⟶ X` to `f ≫ g`. -/
@[simp] theorem preadditiveCoyonedaInt_map_apply {X Y : C} (g : X ⟶ Y) (f : P ⟶ X) :
    (preadditiveCoyonedaInt P).map g f = f ≫ g := rfl

/-- The same map formula for the additive-group-valued functor. -/
theorem preadditiveCoyoneda_obj_map_apply {X Y : C} (g : X ⟶ Y) (f : P ⟶ X) :
    (preadditiveCoyoneda.obj (op P)).map g f = f ≫ g := rfl

/-- The same map formula for the right `End P`-module functor. -/
theorem preadditiveCoyonedaObj_map_apply {X Y : C} (g : X ⟶ Y) (f : P ⟶ X) :
    (preadditiveCoyonedaObj P).map g f = f ≫ g := rfl

/-- The right `End P`-action: `MulOpposite.op r` acts on `f : P ⟶ X` as `f · r = r ≫ f`. -/
theorem preadditiveCoyonedaObj_op_smul (X : C) (r : End P)
    (f : (preadditiveCoyonedaObj P).obj X) :
    MulOpposite.op r • f = r ≫ f := rfl

/-- The right-module law `f · (r * s) = (f · r) · s`, where `r * s = s ≫ r`. -/
theorem preadditiveCoyonedaObj_op_mul_smul (X : C) (r s : End P)
    (f : (preadditiveCoyonedaObj P).obj X) :
    MulOpposite.op (r * s) • f = MulOpposite.op s • MulOpposite.op r • f := by
  rw [MulOpposite.op_mul, mul_smul]

/-! The integer action below is written with the module structure `isModule` of the object of
`ModuleCat ℤ` explicitly: plain `n • f` on the carrier would be elaborated with the additive
group's own `ℤ`-action instead of the restricted one. -/

/-- The restricted integer action is the action of the integer endomorphism `(n : End P)`. -/
theorem preadditiveCoyonedaInt_smul_eq_comp (X : C) (n : ℤ) (f : P ⟶ X) :
    ((preadditiveCoyonedaInt P).obj X).isModule.smul n f = (n : End P) ≫ f := rfl

/-- The restricted integer action is ordinary repeated addition in `P ⟶ X`. -/
theorem preadditiveCoyonedaInt_smul (X : C) (n : ℤ) (f : P ⟶ X) :
    ((preadditiveCoyonedaInt P).obj X).isModule.smul n f = n • f :=
  int_smul_eq_zsmul ((preadditiveCoyonedaInt P).obj X).isModule n f

/-- The restricted `ℤ`-module structure on `P ⟶ X` is the canonical one of its additive group. -/
theorem preadditiveCoyonedaInt_obj_isModule (X : C) :
    ((preadditiveCoyonedaInt P).obj X).isModule = AddCommGroup.toIntModule (P ⟶ X) :=
  Subsingleton.elim _ _

/-- After `forget₂`, the integer-module functor is definitionally the group-valued Hom functor. -/
theorem preadditiveCoyonedaInt_comp_forget₂ :
    preadditiveCoyonedaInt P ⋙ forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v} =
      preadditiveCoyoneda.obj (op P) := rfl

/-- The natural isomorphism, with identity components, from the integer-module Hom functor
followed by `forget₂` to Mathlib's additive-group-valued `Hom(P, -)`. -/
def preadditiveCoyonedaIntCompForget₂Iso :
    preadditiveCoyonedaInt P ⋙ forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v} ≅
      preadditiveCoyoneda.obj (op P) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

@[simp] theorem preadditiveCoyonedaIntCompForget₂Iso_hom_app_apply (X : C) (f : P ⟶ X) :
    (preadditiveCoyonedaIntCompForget₂Iso P).hom.app X f = f := rfl

@[simp] theorem preadditiveCoyonedaIntCompForget₂Iso_inv_app_apply (X : C) (f : P ⟶ X) :
    (preadditiveCoyonedaIntCompForget₂Iso P).inv.app X f = f := rfl

/-- The integer-module Hom functor is additive. -/
theorem preadditiveCoyonedaInt_additive : (preadditiveCoyonedaInt P).Additive := inferInstance

/-- The covariant integer-module Hom functor preserves sums of morphisms. -/
theorem preadditiveCoyonedaInt_map_add {X Y : C} (g g' : X ⟶ Y) :
    (preadditiveCoyonedaInt P).map (g + g') =
      (preadditiveCoyonedaInt P).map g + (preadditiveCoyonedaInt P).map g' :=
  Functor.map_add _

end Covariant

section Contravariant

/-- Renard's contravariant `Hom_A(•, P) : Aᵒᵖ → ℤ-mod`: the left `End P`-module functor
`preadditiveYonedaObj P` with scalars restricted along `ℤ → End P`. -/
abbrev preadditiveYonedaInt (P : C) : Cᵒᵖ ⥤ ModuleCat.{v} ℤ :=
  preadditiveYonedaObj P ⋙ ModuleCat.restrictScalars (Int.castRingHom (End P))

variable (P : C)

/-- The carrier of `Hom_A(X, P)` is the Hom type `X ⟶ P`. -/
theorem preadditiveYonedaInt_obj_carrier (X : C) :
    ((preadditiveYonedaInt P).obj (op X) : Type v) = (X ⟶ P) := rfl

/-- The contravariant Hom map on `g.op` sends `h : Y ⟶ P` to `g ≫ h`. -/
@[simp] theorem preadditiveYonedaInt_map_apply {X Y : C} (g : X ⟶ Y) (h : Y ⟶ P) :
    (preadditiveYonedaInt P).map g.op h = g ≫ h := rfl

/-- The same map formula for the additive-group-valued functor. -/
theorem preadditiveYoneda_obj_map_apply {X Y : C} (g : X ⟶ Y) (h : Y ⟶ P) :
    (preadditiveYoneda.obj P).map g.op h = g ≫ h := rfl

/-- The same map formula for the left `End P`-module functor. -/
theorem preadditiveYonedaObj_map_apply {X Y : C} (g : X ⟶ Y) (h : Y ⟶ P) :
    (preadditiveYonedaObj P).map g.op h = g ≫ h := rfl

/-- The left `End P`-action: `r` acts on `h : X ⟶ P` as `h ≫ r`. -/
theorem preadditiveYonedaObj_smul (X : C) (r : End P)
    (h : (preadditiveYonedaObj P).obj (op X)) :
    r • h = h ≫ r := rfl

/-- The left-module law `(r * s) · h = r · (s · h)`, where `r * s = s ≫ r`. -/
theorem preadditiveYonedaObj_mul_smul (X : C) (r s : End P)
    (h : (preadditiveYonedaObj P).obj (op X)) :
    (r * s) • h = r • s • h :=
  mul_smul r s h

/-- The restricted integer action is the action of the integer endomorphism `(n : End P)`. -/
theorem preadditiveYonedaInt_smul_eq_comp (X : C) (n : ℤ) (h : X ⟶ P) :
    ((preadditiveYonedaInt P).obj (op X)).isModule.smul n h = h ≫ (n : End P) := rfl

/-- The restricted integer action is ordinary repeated addition in `X ⟶ P`. -/
theorem preadditiveYonedaInt_smul (X : C) (n : ℤ) (h : X ⟶ P) :
    ((preadditiveYonedaInt P).obj (op X)).isModule.smul n h = n • h :=
  int_smul_eq_zsmul ((preadditiveYonedaInt P).obj (op X)).isModule n h

/-- The restricted `ℤ`-module structure on `X ⟶ P` is the canonical one of its additive group. -/
theorem preadditiveYonedaInt_obj_isModule (X : C) :
    ((preadditiveYonedaInt P).obj (op X)).isModule = AddCommGroup.toIntModule (X ⟶ P) :=
  Subsingleton.elim _ _

/-- After `forget₂`, the integer-module functor is definitionally the group-valued Hom functor. -/
theorem preadditiveYonedaInt_comp_forget₂ :
    preadditiveYonedaInt P ⋙ forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v} =
      preadditiveYoneda.obj P := rfl

/-- The natural isomorphism, with identity components, from the integer-module Hom functor
followed by `forget₂` to Mathlib's additive-group-valued `Hom(-, P)`. -/
def preadditiveYonedaIntCompForget₂Iso :
    preadditiveYonedaInt P ⋙ forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v} ≅
      preadditiveYoneda.obj P :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

@[simp] theorem preadditiveYonedaIntCompForget₂Iso_hom_app_apply (X : C) (h : X ⟶ P) :
    (preadditiveYonedaIntCompForget₂Iso P).hom.app (op X) h = h := rfl

@[simp] theorem preadditiveYonedaIntCompForget₂Iso_inv_app_apply (X : C) (h : X ⟶ P) :
    (preadditiveYonedaIntCompForget₂Iso P).inv.app (op X) h = h := rfl

/-- The integer-module Hom functor is additive. -/
theorem preadditiveYonedaInt_additive : (preadditiveYonedaInt P).Additive := inferInstance

/-- The contravariant integer-module Hom functor preserves sums of morphisms. -/
theorem preadditiveYonedaInt_map_add {X Y : Cᵒᵖ} (g g' : X ⟶ Y) :
    (preadditiveYonedaInt P).map (g + g') =
      (preadditiveYonedaInt P).map g + (preadditiveYonedaInt P).map g' :=
  Functor.map_add _

end Contravariant

/-- Renard's abelian setting is a special case of the preadditive construction. -/
example {A : Type u} [Category.{v} A] [Abelian A] (P : A) :
    (A ⥤ ModuleCat.{v} ℤ) × (Aᵒᵖ ⥤ ModuleCat.{v} ℤ) :=
  (preadditiveCoyonedaInt P, preadditiveYonedaInt P)

end Langlands.CategoryTheory.Renard
