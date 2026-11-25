/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Pushing `Ext`-classes along an exact functor, in the derived category

Let `F : C ⥤ D` be an exact functor between abelian categories and `Φ : D(C) ⥤ D(D)` a functor
commuting with the shifts, identified with `F.mapDerivedCategory` by an isomorphism compatible
with the shifts (e.g. a total derived functor of `F`). For isomorphisms `F X ≅ X'`, `F Y ≅ Y'`,
pushing a class `e ∈ Extⁿ(X, Y)` forward along `F` and transporting it to `Extⁿ(X', Y')` is,
as a morphism `X' ⟶ Y'[n]` of the derived category, the morphism `Φ(e)` read through the induced
isomorphisms `Φ X ≅ X'`, `Φ Y ≅ Y'`
(`CategoryTheory.Abelian.Ext.mapExactFunctor_conj_hom`).
-/

@[expose] public section

universe w w' t t' v v' u u'

namespace CategoryTheory.Abelian.Ext

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D] [HasExt.{w} C] [HasExt.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {Φ : DerivedCategory C ⥤ DerivedCategory D} [Φ.CommShift ℤ]
  (θ : Φ ≅ F.mapDerivedCategory) [NatTrans.CommShift θ.hom ℤ]

/-- **`Ext`-classes pushed along an exact functor, in the derived category.** Let
`θ : Φ ≅ F.mapDerivedCategory` be compatible with the shifts, and `εX : Φ X ≅ X'`,
`εY : Φ Y ≅ Y'` the isomorphisms induced by `θ` and isomorphisms `αX : F X ≅ X'`,
`αY : F Y ≅ Y'`. Then the class `αX⁻¹ ∘ F(e) ∘ αY` of `Extⁿ(X', Y')` is the morphism
`εX⁻¹ ≫ Φ(e) ≫ εY[n]`. -/
theorem mapExactFunctor_conj_hom {X Y : C} {X' Y' : D} (αX : F.obj X ≅ X') (αY : F.obj Y ≅ Y')
    (εX : Φ.obj ((DerivedCategory.singleFunctor C 0).obj X) ≅
      (DerivedCategory.singleFunctor D 0).obj X')
    (εY : Φ.obj ((DerivedCategory.singleFunctor C 0).obj Y) ≅
      (DerivedCategory.singleFunctor D 0).obj Y')
    (hεX : εX.hom = θ.hom.app _ ≫ (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
      (DerivedCategory.singleFunctor D 0).map αX.hom)
    (hεY : εY.hom = θ.hom.app _ ≫ (F.mapDerivedCategorySingleFunctor 0).hom.app Y ≫
      (DerivedCategory.singleFunctor D 0).map αY.hom)
    {n : ℕ} (e : Ext.{w} X Y n) :
    ((mk₀ αX.inv).comp ((e.mapExactFunctor F).comp (mk₀ αY.hom) (add_zero n))
        (zero_add n)).hom =
      εX.inv ≫ Φ.map e.hom ≫ (Φ.commShiftIso (n : ℤ)).hom.app _ ≫ εY.hom⟦(n : ℤ)⟧' := by
  have hεX' : εX.inv = (DerivedCategory.singleFunctor D 0).map αX.inv ≫
      (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫ θ.inv.app _ := by
    rw [← cancel_epi εX.hom, Iso.hom_inv_id, hεX]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id,
      Category.id_comp, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  rw [comp_hom, comp_hom, mk₀_hom, mk₀_hom, mapExactFunctor_hom, ShiftedHom.comp_mk₀,
    ShiftedHom.mk₀_comp, hεX', hεY, ShiftedHom.map]
  simp only [Functor.map_comp, Category.assoc,
    NatTrans.shift_app_comm_assoc θ.hom (n : ℤ)]
  rw [θ.hom.naturality_assoc, Iso.inv_hom_id_app_assoc]

end CategoryTheory.Abelian.Ext
