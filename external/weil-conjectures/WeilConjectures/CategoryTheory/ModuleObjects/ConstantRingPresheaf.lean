/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Module objects over a constant ring presheaf

Let `T` be a ring and `C` a category. The constant presheaf `T` on `C` is a ring object of the
category `Cᵒᵖ ⥤ Ab` of abelian presheaves, with its objectwise tensor product
(`CategoryTheory.Presheaf.constRingObj`). A module object over it is an abelian presheaf `M`
with an action
`T ⊗ M(U) ⟶ M(U)`, unital, associative and natural in `U`, that is a presheaf of `T`-modules.

## Main definitions

* `CategoryTheory.Presheaf.modToModule`: the presheaf of `T`-modules underlying a module object
  over the constant ring presheaf `T`, with `t • x` given by the action on `t ⊗ x`.
* `CategoryTheory.Presheaf.moduleToMod`: conversely, a presheaf of `T`-modules as a module object.
* `CategoryTheory.Presheaf.modConstRingEquivalence`: these are inverse equivalences
  `Mod (Cᵒᵖ ⥤ Ab) T ≌ (Cᵒᵖ ⥤ ModuleCat T)`. Both functors keep the underlying abelian presheaf.
-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AddCommGrpCat

variable (T : Type w) [Ring T]

/-- The action `T ⊗ M ⟶ M` of a `T`-module on its underlying abelian group. -/
noncomputable def smulHom (M : Type w) [AddCommGroup M] [Module T M] :
    of T ⊗ of M ⟶ of M :=
  ofHom (TensorProduct.lift (LinearMap.mk₂ ℤ (fun (r : T) (x : M) ↦ r • x)
    (fun _ _ _ ↦ add_smul _ _ _) (fun c r x ↦ (smul_assoc c r x :))
    (fun _ _ _ ↦ smul_add _ _ _) (fun c r x ↦ smul_comm r c x))).toAddMonoidHom

@[simp]
lemma smulHom_tmul (M : Type w) [AddCommGroup M] [Module T M] (r : T) (x : M) :
    (smulHom T M).hom (r ⊗ₜ[ℤ] x) = r • x :=
  rfl

end AddCommGrpCat

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] (T : Type w) [Ring T]

/-- The constant presheaf with value the ring `T`, as a ring object of abelian presheaves. -/
abbrev constRingObj : Cᵒᵖ ⥤ Ab.{w} :=
  (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of T)

lemma constRingObj_one_app (U : Cᵒᵖ) :
    (η[constRingObj (C := C) T]).app U = η[AddCommGrpCat.of T] :=
  rfl

lemma constRingObj_mul_app (U : Cᵒᵖ) :
    (μ[constRingObj (C := C) T]).app U = μ[AddCommGrpCat.of T] :=
  rfl


/-- The constant ring presheaf of a commutative ring is a commutative ring object. -/
instance isCommMonObj_constRingObj (T : Type w) [CommRing T] :
    IsCommMonObj (constRingObj (C := C) T) where
  mul_comm := NatTrans.ext (funext fun _ ↦ AddCommGrpCat.hom_ext_toIntLinearMap
    (TensorProduct.ext' fun (a b : T) ↦ mul_comm b a))

/-- The action of the constant ring presheaf on the abelian presheaf underlying a presheaf of
`T`-modules. -/
noncomputable def smulNatTrans (N : Cᵒᵖ ⥤ ModuleCat.{w} T) :
    constRingObj T ⊗ (N ⋙ forget₂ (ModuleCat.{w} T) Ab.{w}) ⟶
      N ⋙ forget₂ (ModuleCat.{w} T) Ab.{w} where
  app U := AddCommGrpCat.smulHom T (N.obj U)
  naturality _ _ f := AddCommGrpCat.hom_ext_toIntLinearMap
    (TensorProduct.ext' fun r x ↦ ((N.map f).hom.map_smul r x).symm)

/-- A presheaf of `T`-modules as a module object over the constant ring presheaf `T`. -/
noncomputable def toMod (N : Cᵒᵖ ⥤ ModuleCat.{w} T) :
    Mod (Cᵒᵖ ⥤ Ab.{w}) (constRingObj (C := C) T) where
  X := N ⋙ forget₂ (ModuleCat.{w} T) Ab.{w}
  mod := ModObj.mk' _ (smulNatTrans T N)
    (NatTrans.ext (funext fun U ↦ AddCommGrpCat.hom_ext_toIntLinearMap
      (TensorProduct.ext' fun n (x : N.obj U) ↦ (Int.cast_smul_eq_zsmul T n.down x :))))
    (NatTrans.ext (funext fun U ↦ AddCommGrpCat.hom_ext_toIntLinearMap
      (TensorProduct.ext_threefold fun (a b : T) (x : N.obj U) ↦ (mul_smul a b x :))))

variable {T}

section OfMod

variable (M : Mod (Cᵒᵖ ⥤ Ab.{w}) (constRingObj (C := C) T))

/-- The component at `U` of the action of the constant ring presheaf `T` on a module object. -/
noncomputable abbrev actApp (U : Cᵒᵖ) :
    AddCommGrpCat.of T ⊗ M.X.obj U ⟶ M.X.obj U :=
  (Mod.act (A := constRingObj (C := C) T) M.X).app U

/-- The component at `U` of the action, as an additive map out of the tensor product. -/
noncomputable abbrev actHom (U : Cᵒᵖ) : TensorProduct ℤ T (M.X.obj U) →+ M.X.obj U :=
  (actApp M U).hom

/-- The action of `a : T` on the sections over `U` of a module object over the constant ring
presheaf `T`. -/
noncomputable def modSmul (U : Cᵒᵖ) (a : T) (x : M.X.obj U) : M.X.obj U :=
  actHom M U (a ⊗ₜ[ℤ] x)

lemma modSmul_one (U : Cᵒᵖ) (x : M.X.obj U) : modSmul M U 1 x = x := by
  have h := congrArg (fun f ↦ (f.app U).hom (ULift.up (1 : ℤ) ⊗ₜ[ℤ] x))
    (Mod.one_act (A := constRingObj (C := C) T) M.X)
  have h' : modSmul M U ((1 : ℤ) : T) x = (1 : ℤ) • x := h
  rwa [Int.cast_one, one_smul] at h'

lemma modSmul_mul (U : Cᵒᵖ) (a b : T) (x : M.X.obj U) :
    modSmul M U (a * b) x = modSmul M U a (modSmul M U b x) := by
  have h := congrArg (fun f ↦ (f.app U).hom ((a ⊗ₜ[ℤ] b) ⊗ₜ[ℤ] x))
    (Mod.mul_act (A := constRingObj (C := C) T) M.X)
  exact h

lemma modSmul_add (U : Cᵒᵖ) (a : T) (x y : M.X.obj U) :
    modSmul M U a (x + y) = modSmul M U a x + modSmul M U a y := by
  rw [modSmul, TensorProduct.tmul_add, map_add]
  rfl

lemma add_modSmul (U : Cᵒᵖ) (a b : T) (x : M.X.obj U) :
    modSmul M U (a + b) x = modSmul M U a x + modSmul M U b x := by
  rw [modSmul, modSmul, modSmul, ← map_add, ← TensorProduct.add_tmul]

lemma modSmul_zero (U : Cᵒᵖ) (a : T) : modSmul M U a 0 = 0 := by
  rw [modSmul, TensorProduct.tmul_zero, map_zero]

lemma zero_modSmul (U : Cᵒᵖ) (x : M.X.obj U) : modSmul M U 0 x = 0 := by
  rw [modSmul, ← map_zero (actHom M U), ← TensorProduct.zero_tmul _ x]

/-- The restriction maps of a module object over the constant ring presheaf commute with the
action of `T`. -/
lemma map_modSmul {U V : Cᵒᵖ} (f : U ⟶ V) (a : T) (x : M.X.obj U) :
    (M.X.map f).hom (modSmul M U a x) = modSmul M V a ((M.X.map f).hom x) :=
  congrArg (fun g ↦ g.hom (a ⊗ₜ[ℤ] x))
    ((Mod.act (A := constRingObj (C := C) T) M.X).naturality f).symm

/-- The `T`-module structure on the sections over `U` of a module object over the constant ring
presheaf `T`. -/
noncomputable instance componentModule (U : Cᵒᵖ) : Module T (M.X.obj U) where
  smul := modSmul M U
  one_smul := modSmul_one M U
  mul_smul := modSmul_mul M U
  smul_zero := modSmul_zero M U
  smul_add := modSmul_add M U
  add_smul a b := add_modSmul M U a b
  zero_smul := zero_modSmul M U

/-- The presheaf of `T`-modules underlying a module object over the constant ring presheaf `T`. -/
noncomputable def ofMod : Cᵒᵖ ⥤ ModuleCat.{w} T where
  obj U :=
    ModuleCat.of T (M.X.obj U)
  map {U V} f :=
    ModuleCat.ofHom
      { toFun := (M.X.map f).hom
        map_add' := map_add _
        map_smul' := map_modSmul M f }
  map_id U := by
    ext
    simp
  map_comp f g := by
    ext
    simp

end OfMod

variable {M M' : Mod (Cᵒᵖ ⥤ Ab.{w}) (constRingObj (C := C) T)}

/-- A morphism of module objects commutes with the action of `T` on sections. -/
lemma hom_app_modSmul (g : M ⟶ M') (U : Cᵒᵖ) (a : T) (x : M.X.obj U) :
    (g.hom.app U).hom (modSmul M U a x) = modSmul M' U a ((g.hom.app U).hom x) :=
  congrArg (fun k ↦ (k.app U).hom (a ⊗ₜ[ℤ] x)) (Mod.act_hom g)

variable (T) in
/-- Module objects over the constant ring presheaf `T` are presheaves of `T`-modules. -/
noncomputable def modToModule :
    Mod (Cᵒᵖ ⥤ Ab.{w}) (constRingObj (C := C) T) ⥤ (Cᵒᵖ ⥤ ModuleCat.{w} T) where
  obj := ofMod
  map {M M'} g :=
    { app U :=
        ModuleCat.ofHom
          { toFun := (g.hom.app U).hom
            map_add' := map_add _
            map_smul' := hom_app_modSmul g U }
      naturality U V f := ModuleCat.hom_ext (LinearMap.ext fun x ↦
        congrArg (fun k ↦ k.hom x) (g.hom.naturality f)) }

variable (T) in
/-- Presheaves of `T`-modules are module objects over the constant ring presheaf `T`. -/
noncomputable def moduleToMod :
    (Cᵒᵖ ⥤ ModuleCat.{w} T) ⥤ Mod (Cᵒᵖ ⥤ Ab.{w}) (constRingObj (C := C) T) where
  obj := toMod T
  map {N N'} g := Mod.homMk (Functor.whiskerRight g (forget₂ (ModuleCat.{w} T) Ab.{w}))
    (NatTrans.ext (funext fun U ↦ AddCommGrpCat.hom_ext_toIntLinearMap
      (TensorProduct.ext' fun r (x : N.obj U) ↦ ((g.app U).hom.map_smul r x))))

/-- A module object over the constant ring presheaf `T` is recovered from its presheaf of
`T`-modules. -/
noncomputable def unitIsoApp (M : Mod (Cᵒᵖ ⥤ Ab.{w}) (constRingObj (C := C) T)) :
    M ≅ (moduleToMod T).obj ((modToModule T).obj M) :=
  Mod.isoMk (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl)
    (NatTrans.ext (funext fun _ ↦ AddCommGrpCat.hom_ext_toIntLinearMap
      (TensorProduct.ext' fun _ _ ↦ rfl)))

/-- A presheaf of `T`-modules is recovered from its module object. -/
noncomputable def counitIsoApp (N : Cᵒᵖ ⥤ ModuleCat.{w} T) :
    (modToModule T).obj ((moduleToMod T).obj N) ≅ N :=
  NatIso.ofComponents
    (fun U ↦ LinearEquiv.toModuleIso (X₁ := (toMod T N).X.obj U) (X₂ := N.obj U)
      (m₁ := componentModule (toMod T N) U)
      { toFun := id
        invFun := id
        map_add' _ _ := rfl
        map_smul' _ _ := rfl
        left_inv _ := rfl
        right_inv _ := rfl })
    fun _ ↦ rfl

variable (C T) in
/-- Module objects over the constant ring presheaf `T` in abelian presheaves are the
presheaves of `T`-modules. -/
noncomputable def modConstRingEquivalence :
    Mod (Cᵒᵖ ⥤ Ab.{w}) (constRingObj (C := C) T) ≌ (Cᵒᵖ ⥤ ModuleCat.{w} T) :=
  CategoryTheory.Equivalence.mk (modToModule T) (moduleToMod T)
    (NatIso.ofComponents unitIsoApp fun _ ↦ Mod.hom_ext _ _ rfl)
    (NatIso.ofComponents counitIsoApp fun _ ↦ by ext; rfl)

end CategoryTheory.Presheaf
