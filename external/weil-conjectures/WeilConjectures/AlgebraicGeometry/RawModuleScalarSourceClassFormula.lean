/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison


public import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourcePrefix
import all WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted
import WeilConjectures.AlgebraicGeometry.RawModuleScalarSheafComposition
import WeilConjectures.AlgebraicGeometry.RawModuleScalarSourceSquareCore

/-! # Source and class coherence before coefficients

Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: lem-sbc-raw-module-scalar-source-class-formula).
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

private theorem sheaf_source_attach
    {E B : Type*} [Category E] [Category B]
    (H : E ⥤ B) {A₁ A₂ A₃ A₄ : B} {B₁ B₂ B₃ : E}
    (f : A₁ ⟶ A₂) (p : A₂ ⟶ A₃) (v : A₃ ⟶ A₄)
    (kL : A₂ ⟶ H.obj B₂) (kE : A₁ ⟶ H.obj B₁)
    (g : B₁ ⟶ B₂) (q : B₂ ⟶ B₃) (r : H.obj B₃ ⟶ A₄)
    (ht : f ≫ kL = kE ≫ H.map g)
    (hc : p ≫ v = kL ≫ H.map q ≫ r) :
    (f ≫ p) ≫ v = kE ≫ H.map (g ≫ q) ≫ r := by
  rw [Category.assoc, hc, ← Category.assoc, ht]
  simp only [Functor.map_comp, Category.assoc]

private theorem source_class_attach
    {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    (M : C₀ ⥤ C₁) (VA : C₁ ⥤ D₁) (VB : C₀ ⥤ D₀) (H : D₀ ⥤ D₁)
    (e : M ⋙ VA ≅ VB ⋙ H)
    {X Y : C₀} {EA : D₁} {EB : D₀} {LA : C₁}
    (cA : EA ⟶ VA.obj LA) (cB : EB ⟶ VB.obj X)
    (m : LA ⟶ M.obj X) (a : EA ⟶ H.obj EB) (z : X ⟶ Y)
    (hs : cA ≫ VA.map m = a ≫ H.map cB ≫ e.inv.app X) :
    cA ≫ VA.map m ≫ VA.map (M.map z) =
      (a ≫ H.map (cB ≫ VB.map z)) ≫ e.inv.app Y := by
  rw [← Category.assoc, hs]
  simp only [Category.assoc, Functor.map_comp]
  have hn := e.inv.naturality z
  change H.map (VB.map z) ≫ e.inv.app Y = e.inv.app X ≫ VA.map (M.map z) at hn
  rw [← hn]

private theorem single_source_class_attach
    {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]
    [Abelian C] [Abelian D] [Abelian E] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory B]
    (M : C ⥤ D) (V' : D ⥤ B) (V : C ⥤ E) (H : E ⥤ B)
    [M.Additive] [V'.Additive] [V.Additive] [H.Additive]
    [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    [PreservesFiniteLimits V'] [PreservesFiniteColimits V']
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : M ⋙ V' ≅ V ⋙ H) (n : ℤ)
    {LA : D} {LB : C} {EA : B} {EB : E}
    (m : LA ⟶ M.obj LB) (a : EA ⟶ H.obj EB)
    (cA : EA ⟶ V'.obj LA) (cB : EB ⟶ V.obj LB)
    {Y : DerivedCategory.Plus C} (z : (DerivedCategory.Plus.singleFunctor C n).obj LB ⟶ Y)
    (hs : cA ≫ V'.map m = a ≫ H.map cB ≫ e.inv.app LB) :
    ((DerivedCategory.Plus.singleFunctor B n).map cA ≫
        (V'.mapDerivedCategoryPlusSingleFunctor n).inv.app LA) ≫
      V'.mapDerivedCategoryPlus.map
        ((DerivedCategory.Plus.singleFunctor D n).map m ≫
          (M.mapDerivedCategoryPlusSingleFunctor n).inv.app LB) ≫
      V'.mapDerivedCategoryPlus.map (M.mapDerivedCategoryPlus.map z) =
    (((DerivedCategory.Plus.singleFunctor B n).map a ≫
        (H.mapDerivedCategoryPlusSingleFunctor n).inv.app EB) ≫
      H.mapDerivedCategoryPlus.map
        (((DerivedCategory.Plus.singleFunctor E n).map cB ≫
            (V.mapDerivedCategoryPlusSingleFunctor n).inv.app LB) ≫
          V.mapDerivedCategoryPlus.map z)) ≫
      ((Functor.mapDerivedCategoryPlusCompIso M V').symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso e ≪≫
          Functor.mapDerivedCategoryPlusCompIso V H).inv.app Y := by
  exact source_class_attach M.mapDerivedCategoryPlus V'.mapDerivedCategoryPlus
    V.mapDerivedCategoryPlus H.mapDerivedCategoryPlus
    ((Functor.mapDerivedCategoryPlusCompIso M V').symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso e ≪≫ Functor.mapDerivedCategoryPlusCompIso V H)
    _ _ _ _ z (Functor.plus_single_source_square_core M V' V H e n m a cA cB hs)

set_option backward.isDefEq.respectTransparency false in
/-- Commute the source and class factors before attaching any coefficient tail.
Source: Stacks Project, Tags 03D7 and 03Q8, scalar inverse-image composition.
(blueprint: lem-sbc-raw-module-scalar-source-class-formula).

Proof: Apply rawModuleScalar_sheaf_composition to the free represented module
sheaf. Naturality of upperStarComp on the free abelian generator attaches that
generator to its source square. Apply plus_single_source_square_core in degree
zero to derive the square. Its factors are scalarSourceFactor, moduleSourceFactor
and abelianSourceFactor, and its comparison is derivedPullbackIso. Postcompose
this square with derived scalar forgetting of the derived inverse image of z.
Naturality of the inverse derivedPullbackIso on z moves z across the inverse
comparison. Functor.map_comp combines the abelian inverse images of the source
map and forgotten class into rawModuleScalarSourcePrefix. Reassociate. No
moduleCoefficientFactor, scalarCoefficientFactor or coefficient coherence is
used in this equation. Zero classes, q = 0, identity arrows, zero and empty
objects satisfy the same functoriality and naturality equations.
-/
theorem rawModuleScalar_source_class_formula
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    scalarSourceFactor Λ (A.hom ≫ k) ((freeSheaf Λ S).obj U)
        (RawModuleScalarComparison.freeAbelian S U)
        (RawModuleScalarComparison.freeMap Λ S U) ≫
      (moduleAbelianForget Λ A.left).mapDerivedCategoryPlus.map
        (moduleSourceFactor Λ f.left (B.hom ≫ k) (A.hom ≫ k)
          (by rw [← Category.assoc, Over.w]) ((freeSheaf Λ S).obj U)) ≫
      (moduleAbelianForget Λ A.left).mapDerivedCategoryPlus.map
        ((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.map z) =
    rawModuleScalarSourcePrefix Λ k G q U A B f z ≫
      (moduleAbelianDerivedUpperStarIso Λ f.left).hom.app
        (((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G))⟦(q : ℤ)⟧) := by
  let L := (freeSheaf Λ S).obj U
  let E := RawModuleScalarComparison.freeAbelian S U
  let t := RawModuleScalarComparison.freeMap Λ S U
  let M := upperStar (ModuleCat.{u + 1} Λ) f.left
  let V' := moduleAbelianForget Λ A.left
  let V := moduleAbelianForget Λ B.left
  let H := upperStar AddCommGrpCat.{u + 1} f.left
  let e := RawModuleScalarComparison.pullbackIso Λ f.left
  let w : f.left ≫ (B.hom ≫ k) = A.hom ≫ k := by rw [← Category.assoc, Over.w]
  let m := (upperStarComp (ModuleCat.{u + 1} Λ) f.left (B.hom ≫ k)
    (A.hom ≫ k) w.symm).hom.app L
  let a := (upperStarComp AddCommGrpCat.{u + 1} f.left (B.hom ≫ k)
    (A.hom ≫ k) w.symm).hom.app E
  let cA := (upperStar AddCommGrpCat.{u + 1} (A.hom ≫ k)).map t ≫
    RawModuleScalarComparison.pullback Λ (A.hom ≫ k) L
  let cB := (upperStar AddCommGrpCat.{u + 1} (B.hom ≫ k)).map t ≫
    RawModuleScalarComparison.pullback Λ (B.hom ≫ k) L
  have hs : cA ≫ V'.map m = a ≫ H.map cB ≫
      RawModuleScalarComparison.pullback Λ f.left
        ((upperStar (ModuleCat.{u + 1} Λ) (B.hom ≫ k)).obj L) :=
    sheaf_source_attach H
      ((upperStar AddCommGrpCat.{u + 1} (A.hom ≫ k)).map t)
      (RawModuleScalarComparison.pullback Λ (A.hom ≫ k) L) (V'.map m)
      ((upperStarComp AddCommGrpCat.{u + 1} f.left (B.hom ≫ k) (A.hom ≫ k) w.symm).hom.app
        ((moduleAbelianForget Λ S).obj L)) a
      ((upperStar AddCommGrpCat.{u + 1} (B.hom ≫ k)).map t)
      (RawModuleScalarComparison.pullback Λ (B.hom ≫ k) L)
      (RawModuleScalarComparison.pullback Λ f.left
        ((upperStar (ModuleCat.{u + 1} Λ) (B.hom ≫ k)).obj L))
      ((upperStarComp AddCommGrpCat.{u + 1} f.left (B.hom ≫ k) (A.hom ≫ k) w.symm).hom.naturality t)
      (rawModuleScalar_sheaf_composition Λ f.left (B.hom ≫ k) (A.hom ≫ k) w L)
  simpa only [scalarSourceFactor, moduleSourceFactor, abelianSourceFactor,
    rawTriangleSource, higherDirectImageRawOverComplex,
    rawModuleScalarSourcePrefix, moduleAbelianDerivedUpperStarIso,
    RawModuleScalarComparison.pullbackIso, Functor.plusNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    L, E, t, M, V', V, H, e, w, m, a, cA, cB, Category.assoc] using
    single_source_class_attach
    (Y := ((higherDirectImageRawOverComplex Λ G B)⟦(q : ℤ)⟧))
    M V' V H e 0 m a cA cB z hs

end AlgebraicGeometry.Etale
