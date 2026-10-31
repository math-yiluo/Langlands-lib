import Langlands.Algebra.IntegerCompatibleNonUnitalAction
import Langlands.Algebra.CompatibleUnitization
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence

/-!
# Integer unitization of the category of additive nonunital modules

A derived categorical construction implementing Renard's additive module convention.
The original action has no unit law, including when the acting ring is unital.

`extendFunctor` makes an additive nonunital module into a unital module over
`Unitization ℤ A` by `(n, a) • m = n • m + a • m`; `restrictFunctor` restricts a unital
module along `Unitization.inr`. Both keep carriers and underlying additive maps, and
`equivalence` is the resulting categorical equivalence whose unit and counit are identity
maps. `zeroIntObj` checks the construction on a nonzero group with zero action.
-/

set_option autoImplicit false

open CategoryTheory

namespace Langlands.Algebra.IntegerUnitization

universe u v

variable (A : Type u) [NonUnitalRing A]

/-- Extend the specified action on the same additive group by integer unitization. -/
def extendObj (M : NonUnitalModuleCat.{u, v} A) : ModuleCat.{v} (Unitization ℤ A) :=
  letI := CompatibleUnitization.module
    (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))
  ModuleCat.of (Unitization ℤ A) M

@[simp] theorem extendObj_carrier (M : NonUnitalModuleCat.{u, v} A) :
    (extendObj A M : Type v) = M := rfl

/-- This formula uses the stored module action and the canonical integer action. -/
theorem extendObj_smul (M : NonUnitalModuleCat.{u, v} A)
    (x : Unitization ℤ A) (m : M) :
    (extendObj A M).isModule.smul x m = x.fst • m + x.snd • m := rfl

@[simp] theorem extendObj_inr_smul (M : NonUnitalModuleCat.{u, v} A) (a : A) (m : M) :
    (extendObj A M).isModule.smul (Unitization.inr a : Unitization ℤ A) m = a • m :=
  CompatibleUnitization.inr_smul _ a m

/-- Extension leaves the underlying additive intertwiner unchanged. -/
def extendMap {M N : NonUnitalModuleCat.{u, v} A} (f : NonUnitalModuleHom A M N) :
    extendObj A M ⟶ extendObj A N :=
  letI := CompatibleUnitization.module
    (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))
  letI := CompatibleUnitization.module
    (NonUnitalModule.toIntLinearEndHom (A := A) (V := N))
  ModuleCat.ofHom (CompatibleUnitization.ofLinearIntertwiner f.toIntLinearIntertwiner)

@[simp] theorem extendMap_apply {M N : NonUnitalModuleCat.{u, v} A}
    (f : NonUnitalModuleHom A M N) (m : M) : extendMap A f m = f m := rfl

/-- The actual extension functor to modules over the integer unitization. -/
def extendFunctor : NonUnitalModuleCat.{u, v} A ⥤ ModuleCat.{v} (Unitization ℤ A) where
  obj := extendObj A
  map := extendMap A
  map_id M := by ext m; rfl
  map_comp f g := by ext m; rfl

@[simp] theorem extendFunctor_obj (M : NonUnitalModuleCat.{u, v} A) :
    (extendFunctor A).obj M = extendObj A M := rfl

@[simp] theorem extendFunctor_map {M N : NonUnitalModuleCat.{u, v} A}
    (f : NonUnitalModuleHom A M N) : (extendFunctor A).map f = extendMap A f := rfl

@[simp] theorem extendMap_id (M : NonUnitalModuleCat.{u, v} A) :
    extendMap A (NonUnitalModuleHom.id A M) = 𝟙 (extendObj A M) := by ext m; rfl

@[simp] theorem extendMap_comp {M N P : NonUnitalModuleCat.{u, v} A}
    (f : NonUnitalModuleHom A M N) (g : NonUnitalModuleHom A N P) :
    extendMap A (g.comp f) = extendMap A f ≫ extendMap A g := by ext m; rfl

/-- Restrict a unitization module along the actual nonunital inclusion of A. -/
@[instance_reducible]
def restrictAction (M : ModuleCat.{v} (Unitization ℤ A)) : NonUnitalModule A M :=
  NonUnitalModule.ofEndHom
    ((Module.toAddMonoidEnd (Unitization ℤ A) M).toNonUnitalRingHom.comp
      (Unitization.inrNonUnitalAlgHom ℤ A : A →ₙ+* Unitization ℤ A))

/-- Restriction preserves the carrier and its additive group. -/
def restrictObj (M : ModuleCat.{v} (Unitization ℤ A)) : NonUnitalModuleCat.{u, v} A :=
  letI := restrictAction A M
  NonUnitalModuleCat.of A M

@[simp] theorem restrictObj_carrier (M : ModuleCat.{v} (Unitization ℤ A)) :
    (restrictObj A M : Type v) = M := rfl

@[simp] theorem restrictObj_smul (M : ModuleCat.{v} (Unitization ℤ A)) (a : A) (m : M) :
    (restrictObj A M).isModule.smul a m = (Unitization.inr a : Unitization ℤ A) • m := rfl

/-- Restriction retains the underlying additive map of every unitization-linear map. -/
def restrictMap {M N : ModuleCat.{v} (Unitization ℤ A)} (f : M ⟶ N) :
    NonUnitalModuleHom A (restrictObj A M) (restrictObj A N) where
  toAddMonoidHom := f.hom.toAddMonoidHom
  map_smul' a m := f.hom.map_smul (Unitization.inr a : Unitization ℤ A) m

@[simp] theorem restrictMap_apply {M N : ModuleCat.{v} (Unitization ℤ A)}
    (f : M ⟶ N) (m : M) : restrictMap A f m = f m := rfl

/-- The actual restriction functor along A → Unitization Int A. -/
def restrictFunctor : ModuleCat.{v} (Unitization ℤ A) ⥤ NonUnitalModuleCat.{u, v} A where
  obj := restrictObj A
  map := restrictMap A
  map_id M := by apply NonUnitalModuleHom.ext; intro m; rfl
  map_comp f g := by apply NonUnitalModuleHom.ext; intro m; rfl

@[simp] theorem restrictFunctor_obj (M : ModuleCat.{v} (Unitization ℤ A)) :
    (restrictFunctor A).obj M = restrictObj A M := rfl

@[simp] theorem restrictFunctor_map {M N : ModuleCat.{v} (Unitization ℤ A)} (f : M ⟶ N) :
    (restrictFunctor A).map f = restrictMap A f := rfl

@[simp] theorem restrictMap_id (M : ModuleCat.{v} (Unitization ℤ A)) :
    restrictMap A (𝟙 M) = NonUnitalModuleHom.id A (restrictObj A M) := by
  apply NonUnitalModuleHom.ext
  intro m
  rfl

@[simp] theorem restrictMap_comp {M N P : ModuleCat.{v} (Unitization ℤ A)}
    (f : M ⟶ N) (g : N ⟶ P) :
    restrictMap A (f ≫ g) = (restrictMap A g).comp (restrictMap A f) := by
  apply NonUnitalModuleHom.ext
  intro m
  rfl

/-- Extension followed by restriction recovers the original, possibly zero, action. -/
@[simp] theorem restrict_extend_smul (M : NonUnitalModuleCat.{u, v} A) (a : A) (m : M) :
    (restrictObj A (extendObj A M)).isModule.smul a m = M.isModule.smul a m :=
  extendObj_inr_smul A M a m

/-- The unit component has identity underlying maps in both directions. -/
def unitComponent (M : NonUnitalModuleCat.{u, v} A) :
    M ≅ restrictObj A (extendObj A M) where
  hom :=
    { toAddMonoidHom := AddMonoidHom.id M
      map_smul' a m := (restrict_extend_smul A M a m).symm }
  inv :=
    { toAddMonoidHom := AddMonoidHom.id M
      map_smul' a m := restrict_extend_smul A M a m }
  hom_inv_id := by apply NonUnitalModuleHom.ext; intro m; rfl
  inv_hom_id := by apply NonUnitalModuleHom.ext; intro m; rfl

@[simp] theorem unitComponent_hom_apply (M : NonUnitalModuleCat.{u, v} A) (m : M) :
    (NonUnitalModuleHom.toAddMonoidHom (A := A) (M := M)
      (N := restrictObj A (extendObj A M)) (unitComponent A M).hom) m = m := rfl

@[simp] theorem unitComponent_inv_apply (M : NonUnitalModuleCat.{u, v} A) (m : M) :
    (NonUnitalModuleHom.toAddMonoidHom (A := A) (M := restrictObj A (extendObj A M))
      (N := M) (unitComponent A M).inv) m = m := rfl

/-- The identity maps give the natural extension-restriction round trip. -/
def unitIso : 𝟭 (NonUnitalModuleCat.{u, v} A) ≅ extendFunctor A ⋙ restrictFunctor A :=
  NatIso.ofComponents (unitComponent A) (by
    intro M N f
    apply NonUnitalModuleHom.ext
    intro m
    rfl)

/-- Every unital integer-unitization module has the canonical integer scalar action. -/
theorem inl_smul (M : ModuleCat.{v} (Unitization ℤ A)) (n : ℤ) (m : M) :
    (Unitization.inl n : Unitization ℤ A) • m = n • m := by
  have hinl : (Unitization.inl n : Unitization ℤ A) = (n : Unitization ℤ A) := by
    exact map_intCast (Unitization.inlRingHom ℤ A) n
  rw [hinl, Int.cast_smul_eq_zsmul]

/-- Restriction and extension recover the whole given action, including its integer part. -/
@[simp] theorem extend_restrict_smul (M : ModuleCat.{v} (Unitization ℤ A))
    (x : Unitization ℤ A) (m : M) :
    (extendObj A (restrictObj A M)).isModule.smul x m = M.isModule.smul x m := by
  change x.fst • m + (Unitization.inr x.snd : Unitization ℤ A) • m = x • m
  conv_rhs => rw [← Unitization.inl_fst_add_inr_snd_eq x]
  rw [_root_.add_smul (Unitization.inl x.fst) (Unitization.inr x.snd : Unitization ℤ A) m,
    inl_smul]

/-- The counit component also has identity underlying maps in both directions. -/
def counitComponent (M : ModuleCat.{v} (Unitization ℤ A)) :
    extendObj A (restrictObj A M) ≅ M where
  hom := ModuleCat.ofHom (X := extendObj A (restrictObj A M)) (Y := M) {
    toFun := fun m => m
    map_add' _ _ := rfl
    map_smul' x m := extend_restrict_smul A M x m }
  inv := ModuleCat.ofHom (X := M) (Y := extendObj A (restrictObj A M)) {
    toFun := fun m => m
    map_add' _ _ := rfl
    map_smul' x m := (extend_restrict_smul A M x m).symm }
  hom_inv_id := by ext m; rfl
  inv_hom_id := by ext m; rfl

@[simp] theorem counitComponent_hom_apply (M : ModuleCat.{v} (Unitization ℤ A)) (m : M) :
    (counitComponent A M).hom m = m := rfl

@[simp] theorem counitComponent_inv_apply (M : ModuleCat.{v} (Unitization ℤ A)) (m : M) :
    (counitComponent A M).inv m = m := rfl

/-- The identity maps give the natural restriction-extension round trip. -/
def counitIso : restrictFunctor A ⋙ extendFunctor A ≅ 𝟭 (ModuleCat.{v} (Unitization ℤ A)) :=
  NatIso.ofComponents (counitComponent A) (by intro M N f; ext m; rfl)

/-- Actual equivalence, with the specified functors and identity unit and counit maps. -/
def equivalence : NonUnitalModuleCat.{u, v} A ≌ ModuleCat.{v} (Unitization ℤ A) where
  functor := extendFunctor A
  inverse := restrictFunctor A
  unitIso := unitIso A
  counitIso := counitIso A
  functor_unitIso_comp M := by ext m; rfl

@[simp] theorem equivalence_functor : (equivalence A).functor = extendFunctor A := rfl

@[simp] theorem equivalence_inverse : (equivalence A).inverse = restrictFunctor A := rfl

@[simp] theorem equivalence_unitIso : (equivalence A).unitIso = unitIso A := rfl

@[simp] theorem equivalence_counitIso : (equivalence A).counitIso = counitIso A := rfl

/-- The forward functor keeps the carrier and the underlying additive map. -/
theorem equivalence_functor_obj_carrier (M : NonUnitalModuleCat.{u, v} A) :
    ((equivalence A).functor.obj M : Type v) = M := rfl

theorem equivalence_functor_map_apply {M N : NonUnitalModuleCat.{u, v} A}
    (f : NonUnitalModuleHom A M N) (m : M) : (equivalence A).functor.map f m = f m := rfl

/-- The inverse functor keeps the carrier and the underlying additive map. -/
theorem equivalence_inverse_obj_carrier (M : ModuleCat.{v} (Unitization ℤ A)) :
    ((equivalence A).inverse.obj M : Type v) = M := rfl

theorem equivalence_inverse_map_apply {M N : ModuleCat.{v} (Unitization ℤ A)}
    (f : M ⟶ N) (m : M) : ((equivalence A).inverse.map f).toAddMonoidHom m = f m := rfl

/-- The unit of the equivalence is the identity map in both directions. -/
theorem equivalence_unitIso_hom_app_apply (M : NonUnitalModuleCat.{u, v} A) (m : M) :
    ((equivalence A).unitIso.hom.app M).toAddMonoidHom m = m := rfl

theorem equivalence_unitIso_inv_app_apply (M : NonUnitalModuleCat.{u, v} A) (m : M) :
    ((equivalence A).unitIso.inv.app M).toAddMonoidHom m = m := rfl

/-- The counit of the equivalence is the identity map in both directions. -/
theorem equivalence_counitIso_hom_app_apply (M : ModuleCat.{v} (Unitization ℤ A)) (m : M) :
    (equivalence A).counitIso.hom.app M m = m := rfl

theorem equivalence_counitIso_inv_app_apply (M : ModuleCat.{v} (Unitization ℤ A)) (m : M) :
    (equivalence A).counitIso.inv.app M m = m := rfl

instance extendFunctor_isEquivalence : (extendFunctor.{u, v} A).IsEquivalence :=
  (equivalence A).isEquivalence_functor

instance restrictFunctor_isEquivalence : (restrictFunctor.{u, v} A).IsEquivalence :=
  (equivalence A).isEquivalence_inverse

/-! The full unapplied types, with independent ring universe `u` and carrier universe `v`. -/

example : (A : Type u) → [NonUnitalRing A] →
    NonUnitalModuleCat.{u, v} A → ModuleCat.{v} (Unitization ℤ A) := @extendObj.{u, v}

example : (A : Type u) → [NonUnitalRing A] → {M N : NonUnitalModuleCat.{u, v} A} →
    NonUnitalModuleHom A M N → (extendObj A M ⟶ extendObj A N) := @extendMap.{u, v}

example : (A : Type u) → [NonUnitalRing A] →
    NonUnitalModuleCat.{u, v} A ⥤ ModuleCat.{v} (Unitization ℤ A) := @extendFunctor.{u, v}

example : (A : Type u) → [NonUnitalRing A] →
    (M : ModuleCat.{v} (Unitization ℤ A)) → NonUnitalModule A M := @restrictAction.{u, v}

example : (A : Type u) → [NonUnitalRing A] →
    ModuleCat.{v} (Unitization ℤ A) → NonUnitalModuleCat.{u, v} A := @restrictObj.{u, v}

example : (A : Type u) → [NonUnitalRing A] → {M N : ModuleCat.{v} (Unitization ℤ A)} →
    (M ⟶ N) → NonUnitalModuleHom A (restrictObj A M) (restrictObj A N) :=
  @restrictMap.{u, v}

example : (A : Type u) → [NonUnitalRing A] →
    ModuleCat.{v} (Unitization ℤ A) ⥤ NonUnitalModuleCat.{u, v} A := @restrictFunctor.{u, v}

example : (A : Type u) → [NonUnitalRing A] →
    NonUnitalModuleCat.{u, v} A ≌ ModuleCat.{v} (Unitization ℤ A) := @equivalence.{u, v}

example : (A : Type) → [NonUnitalRing A] →
    NonUnitalModuleCat.{0, 1} A ≌ ModuleCat.{1} (Unitization ℤ A) := @equivalence.{0, 1}

example : (A : Type 1) → [NonUnitalRing A] →
    NonUnitalModuleCat.{1, 0} A ≌ ModuleCat.{0} (Unitization ℤ A) := @equivalence.{1, 0}

example : Type (max u (v + 1)) := NonUnitalModuleCat.{u, v} A

example : Type (max u (v + 1)) := ModuleCat.{v} (Unitization ℤ A)

example : Category.{v} (NonUnitalModuleCat.{u, v} A) := inferInstance

example : Category.{v} (ModuleCat.{v} (Unitization ℤ A)) := inferInstance

/-- A nonzero additive group with zero original action, even though Int has a unit. -/
abbrev zeroIntObj : NonUnitalModuleCat ℤ :=
  letI : NonUnitalModule ℤ ℤ := NonUnitalModule.zero
  NonUnitalModuleCat.of ℤ ℤ

theorem zeroIntObj_one_ne_zero : (1 : zeroIntObj) ≠ 0 := Int.one_ne_zero

@[simp] theorem zeroIntObj_smul (a m : ℤ) :
    zeroIntObj.isModule.smul a m = 0 := rfl

/-- Restriction of the extension recovers the zero action on this nonzero group. -/
@[simp] theorem zeroIntObj_restrict_extend_smul (a m : ℤ) :
    (restrictObj ℤ (extendObj ℤ zeroIntObj)).isModule.smul a m = 0 := by
  exact restrict_extend_smul ℤ zeroIntObj a m

/-- The old unit still acts as zero after extension along the original-ring inclusion. -/
@[simp] theorem zeroIntObj_old_one_smul (m : ℤ) :
    (extendObj ℤ zeroIntObj).isModule.smul (Unitization.inr (1 : ℤ)) m = 0 := by
  exact extendObj_inr_smul ℤ zeroIntObj 1 m

/-- The new unit acts identically, as required of a module over the unitization. -/
@[simp] theorem zeroIntObj_new_one_smul (m : ℤ) :
    (extendObj ℤ zeroIntObj).isModule.smul (1 : Unitization ℤ ℤ) m = m :=
  (extendObj ℤ zeroIntObj).isModule.one_smul m

end Langlands.Algebra.IntegerUnitization
