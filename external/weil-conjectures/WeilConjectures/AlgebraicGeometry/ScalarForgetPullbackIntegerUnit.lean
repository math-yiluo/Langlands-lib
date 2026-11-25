/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarForgetPullbackComparison

/-! # The integer-unit map and the scalar inverse-image unit

Source: Stacks Project, Tags 0096 and 01F7.
(blueprint: new-sc-scalar-forget-pullback-integer-unit).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme
open Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Sheaf.monoidalCategory

private theorem homEquiv_unique {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G)
    (c : C) (d : D) (v : F'.obj c ⟶ d) :
    a.homEquiv c d ((a.leftAdjointUniq b).hom.app c ≫ v) = b.homEquiv c d v := by
  rw [a.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    b.homEquiv_unit]

private theorem integerUnit_evaluation (k : Type u) [Field k] (X : Scheme.{u}) :
    (((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      isTerminalTop).homEquiv _ _)
        (Abelian.Ext.homEquiv₀ (scalarAbelianUnitClass k X))) (ULift.up (1 : ℤ)) =
      (constantScalarUnitIso (X := X) (k := k)).hom.hom.app (op ⊤)
        (((constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{u} k)
          isTerminalTop).unit.app (ModuleCat.of k k)) (1 : k)) := by
  change (Sheaf.H.equiv₀ _ isTerminalTop) (scalarAbelianUnitClass k X) = _
  unfold scalarAbelianUnitClass
  exact AddEquiv.apply_symm_apply _ _

private theorem scalarOne_inverseUnit (k : Type u) [Field k]
    {X Y : Scheme.{u}} (a : Y ⟶ X) :
    ((scalarInverseUnitIso (k := k) a).inv).hom.app (op ⊤)
      ((constantScalarUnitIso (X := Y) (k := k)).hom.hom.app (op ⊤)
        (((constantSheafAdj (Opens.grothendieckTopology Y) (ModuleCat.{u} k)
          isTerminalTop).unit.app (ModuleCat.of k k)) (1 : k))) =
    (((Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{u} k)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).unit.app
        (𝟙_ (KSheaf X k))).hom.app (op ⊤)
      ((constantScalarUnitIso (X := X) (k := k)).hom.hom.app (op ⊤)
        (((constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{u} k)
          isTerminalTop).unit.app (ModuleCat.of k k)) (1 : k))) := by
  let cX := constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{u} k)
    isTerminalTop
  let cY := constantSheafAdj (Opens.grothendieckTopology Y) (ModuleCat.{u} k)
    isTerminalTop
  let adj := (Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{u} k)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let e := ((Opens.map a.base).constantSheafsheafPullbackIso (ModuleCat.{u} k)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
      isTerminalTop isTerminalTop).app (ModuleCat.of k k)
  let b := (cX.comp adj).ofNatIsoRight
    ((Opens.map a.base).sheafPushforwardContinuousCompSheafSectionsObjIso
      (ModuleCat.{u} k) (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) (op ⊤))
  have he := homEquiv_unique b cY (ModuleCat.of k k) _ e.inv
  change b.homEquiv _ _ (e.hom ≫ e.inv) = cY.homEquiv _ _ e.inv at he
  rw [Iso.hom_inv_id, b.homEquiv_unit, CategoryTheory.Functor.map_id] at he
  erw [Category.comp_id] at he
  rw [cY.homEquiv_unit] at he
  have hv := congrArg (fun m ↦ m (1 : k)) he
  have hn := congrArg (fun m ↦ m.hom.app (op ⊤))
    (adj.unit.naturality (constantScalarUnitIso (X := X) (k := k)).hom)
  unfold scalarInverseUnitIso
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  have hi := ConcreteCategory.congr_hom
    (congrArg (fun m ↦ m.hom.app (op ⊤))
      (constantScalarUnitIso (X := Y) (k := k)).hom_inv_id)
    (cY.unit.app (ModuleCat.of k k) (1 : k))
  change (constantScalarUnitIso (X := Y) (k := k)).inv.hom.app (op ⊤)
    ((constantScalarUnitIso (X := Y) (k := k)).hom.hom.app (op ⊤)
      (cY.unit.app (ModuleCat.of k k) (1 : k))) = _ at hi
  erw [hi]
  dsimp only [b] at hv
  rw [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Adjunction.comp_unit_app] at hv
  simp only [Functor.sheafPushforwardContinuousCompSheafSectionsObjIso,
    ConcreteCategory.comp_apply] at hv
  change (adj.unit.app constantScalarUnit).hom.app (op ⊤)
    (cX.unit.app (ModuleCat.of k k) (1 : k)) =
      e.inv.hom.app (op ⊤) (cY.unit.app (ModuleCat.of k k) (1 : k)) at hv
  erw [← hv]
  have hn' := ConcreteCategory.congr_hom hn (cX.unit.app (ModuleCat.of k k) (1 : k))
  exact hn'.symm

-- The composite sheaf adjunctions require unfolding pointwise evaluation comparisons.
/-- The integer-unit map commutes with the comparison before it is inverted.
Source: Stacks Project, Tags 0096 and 01F7.
(blueprint: new-sc-scalar-forget-pullback-integer-unit).

Proof: Apply the constant-integer sheaf adjunction after transporting along the
constant-integer inverse-image comparison. Its uniqueness-of-left-adjoints
identity changes the adjunction on Y into the composite adjunction on X.
Naturality of the inverse-image adjunction and the adjunct formula for the
comparison reduce the right side to the forgotten scalar inverse-image unit.
Under the integer sections adjunction the unit class is the scalar constant-unit
section of one. The scalar constant-sheaf inverse-image comparison is also the
uniqueness isomorphism of the composite adjunctions; its identity identifies the
left side with that same unit section. Agreement on the integer generator proves
equality, since all maps are additive. The argument includes the empty scheme
and every field characteristic. -/
theorem scalarForgetPullbackComparison_integerUnit (k : Type u) [Field k]
    {X Y : Scheme.{u}} (a : Y ⟶ X) :
    let L := (Opens.map a.base).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
    Abelian.Ext.homEquiv₀ (scalarAbelianUnitClass k Y) ≫
        (scalarAbelianForget k Y).map (scalarInverseUnitIso a).inv =
      (((Opens.map a.base).constantSheafsheafPullbackIso AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
        isTerminalTop isTerminalTop).symm.app (AddCommGrpCat.of (ULift ℤ))).hom ≫
      L.map (Abelian.Ext.homEquiv₀ (scalarAbelianUnitClass k X)) ≫
        (scalarForgetPullbackComparison k a).app (𝟙_ (KSheaf X k)) := by
  let L := (Opens.map a.base).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let cX := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    isTerminalTop
  let cY := constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
    isTerminalTop
  let adj := (Opens.map a.base).sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let e := ((Opens.map a.base).constantSheafsheafPullbackIso AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
      isTerminalTop isTerminalTop).app (AddCommGrpCat.of (ULift ℤ))
  let b := (cX.comp adj).ofNatIsoRight
    ((Opens.map a.base).sheafPushforwardContinuousCompSheafSectionsObjIso
      AddCommGrpCat.{u} (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) (op ⊤))
  let μ := Abelian.Ext.homEquiv₀ (scalarAbelianUnitClass k X)
  let q := L.map μ ≫ (scalarForgetPullbackComparison k a).app (𝟙_ (KSheaf X k))
  have he := homEquiv_unique b cY (AddCommGrpCat.of (ULift ℤ)) _ (e.inv ≫ q)
  change b.homEquiv _ _ (e.hom ≫ (e.inv ≫ q)) = cY.homEquiv _ _ (e.inv ≫ q) at he
  rw [Iso.hom_inv_id_assoc] at he
  apply (cY.homEquiv _ _).injective
  apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
  simp only [AddCommGrpCat.uliftZMultiplesAddEquiv_apply]
  change (uliftZMultiplesHom _).symm _ = (uliftZMultiplesHom _).symm _
  simp only [uliftZMultiplesHom_symm_apply]
  change (cY.homEquiv (AddCommGrpCat.of (ULift ℤ)) _
    (Abelian.Ext.homEquiv₀ (scalarAbelianUnitClass k Y) ≫
      (scalarAbelianForget k Y).map (scalarInverseUnitIso a).inv))
    (ULift.up (1 : ℤ)) =
    (cY.homEquiv _ _ (e.inv ≫ q)) (ULift.up (1 : ℤ))
  rw [← he]
  change (cY.homEquiv (AddCommGrpCat.of (ULift ℤ)) _
    (Abelian.Ext.homEquiv₀ (scalarAbelianUnitClass k Y) ≫
      (scalarAbelianForget k Y).map (scalarInverseUnitIso a).inv))
    (ULift.up (1 : ℤ)) =
    (cX.homEquiv _ _ (adj.homEquiv _ _ q)) (ULift.up (1 : ℤ))
  dsimp only [q, L]
  erw [adj.homEquiv_naturality_left]
  rw [cX.homEquiv_naturality_right, cY.homEquiv_naturality_right]
  have ht := scalarForgetPullbackComparison_adjunct k a
    (𝟙_ (KSheaf X k)) _ (𝟙 _)
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at ht
  conv_rhs at ht => rw [Adjunction.homEquiv_unit]
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at ht
  erw [ht]
  change ((scalarInverseUnitIso a).inv).hom.app (op ⊤)
    ((cY.homEquiv _ _ (Abelian.Ext.homEquiv₀ (scalarAbelianUnitClass k Y)))
      (ULift.up (1 : ℤ))) =
    ((((Opens.map a.base).sheafAdjunctionContinuous (ModuleCat.{u} k) _ _).unit.app
      (𝟙_ (KSheaf X k))).hom.app (op ⊤))
        ((cX.homEquiv _ _ μ) (ULift.up (1 : ℤ)))
  rw [integerUnit_evaluation, integerUnit_evaluation]
  exact scalarOne_inverseUnit k a

end AlgebraicGeometry.Scheme
