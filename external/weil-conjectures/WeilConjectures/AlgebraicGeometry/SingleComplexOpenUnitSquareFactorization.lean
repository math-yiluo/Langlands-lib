/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedComposition
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedCounitUnit

/-! # Normalizing the derived unit through the open pullback square

Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-unit-square-factorization).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem square_factorization
    {C D E A : Type*} [Category C] [Category D] [Category E] [Category A]
    (L₀ : D ⥤ E) (RY : C ⥤ D) (L : C ⥤ A) (RX : A ⥤ E)
    (S : RY ⋙ L₀ ≅ L ⋙ RX)
    {P B : C} {J K : A} {H : D} {W : E}
    (b : P ⟶ B) (k : H ⟶ RY.obj P) (v : L.obj B ⟶ K)
    (e : L.obj P ⟶ J) (t : J ⟶ K) (z : RX.obj K ⟶ W)
    (hc : L.map b ≫ v = e ≫ t) :
    L₀.map (k ≫ RY.map b) ≫ S.hom.app B ≫ RX.map v ≫ z =
      L₀.map k ≫ S.hom.app P ≫ RX.map e ≫ RX.map t ≫ z := by
  simp only [Functor.map_comp, Category.assoc]
  have hn := S.hom.naturality b
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [← RX.map_comp_assoc, hc, RX.map_comp]
  simp only [Category.assoc]

-- Keep derived universal-property constructions abstract during the square calculation.
-- Only the final conversion needs to compare the underlying category instances.
attribute [local irreducible] singleComplexOpenPullbackIso CategoryTheory.Functor.mapDerivedCategory

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option linter.unusedVariables false in
/-- A separate step of the open counit factorization.
Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-unit-square-factorization).

Proof: Put P = F_h(I), beta = F.rightDerivedFunctorUnit(I), and let v be
 the homotopy tensor adjunction counit at I. Apply the pinned derived Hom-equivalence
 compatibility to the homotopy morphism v. The homotopy adjunction sends v to the
 identity of P, so its localized image followed by beta is beta itself. Injectivity
 of the derived Hom equivalence, whose inverse sends beta to Lf(beta) followed by
 the derived counit, gives
 Lf(beta) followed by a_f.counit = epsilon_f(P) followed by Qh(v).
 Let S be the composite natural isomorphism formed by the five displayed factors.
 Its naturality at beta moves Lf0(rY(beta)) from before S to rX(Lf(beta)) after S.
 First distribute Lf0 over the composite with the inverse source factorization.
 Then substitute this naturality equation, combine the two successive rX images,
 apply the normalized counit identity, and distribute rX over its two factors.
 Associativity gives exactly the displayed intermediate composite. This uses no
 tensor comparison cancellation, no boundedness, and no inverse of beta; hence it
 also applies to empty opens and the zero complex. -/
theorem singleComplexOpen_unit_square_factorization
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (I : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let _ : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive :=
      @Classical.choose _ _ exists_derivedPullbackComposition
    let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let F₀ := RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom
    let rY := schemeOpenRestriction Y V
    let rX := schemeOpenRestriction X (f ⁻¹ᵁ V)
    let a := @singleComplexOpenPinnedAdjunction.{u, w} _
    let c := @singleComplexOpenPinnedComposition.{u, w} _
    let ε := @Classical.choose _ _
      (Classical.choose_spec exists_derivedPullbackComposition)
    (derivedPullback (f ∣_ V)).map
        (rY.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
          rY.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app I)) ≫
      ((derivedPullback (f ∣_ V)).mapIso
          ((singleComplexOpenPullbackIso Y V).symm.app
            ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I))) ≪≫
        (c (f ∣_ V) V.ι).app ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)) ≪≫
        eqToIso (congrArg
          (fun k ↦ (derivedPullback k).obj
            ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)))
          (morphismRestrict_ι f V)) ≪≫
        (c (f ⁻¹ᵁ V).ι f).symm.app
          ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)) ≪≫
        (singleComplexOpenPullbackIso X (f ⁻¹ᵁ V)).app
          ((derivedPullback f).obj
            ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)))).hom ≫
      rX.mapDerivedCategory.map ((a f).counit.app (DerivedCategory.Qh.obj I)) ≫
      rX.mapDerivedCategoryFactorsh.hom.app I =
    (derivedPullback (f ∣_ V)).map
      (rY.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      ((derivedPullback (f ∣_ V)).mapIso
          ((singleComplexOpenPullbackIso Y V).symm.app
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I))) ≪≫
        (c (f ∣_ V) V.ι).app (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≪≫
        eqToIso (congrArg
          (fun k ↦ (derivedPullback k).obj
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)))
          (morphismRestrict_ι f V)) ≪≫
        (c (f ⁻¹ᵁ V).ι f).symm.app
          (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≪≫
        (singleComplexOpenPullbackIso X (f ⁻¹ᵁ V)).app
          ((derivedPullback f).obj
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)))).hom ≫
      rX.mapDerivedCategory.map ((ε f).app ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      rX.mapDerivedCategory.map (DerivedCategory.Qh.map
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
          |>.mapHomotopyCategory (.up ℤ)).counit.app I)) ≫
      rX.mapDerivedCategoryFactorsh.hom.app I := by
  classical
  intro hAdd F _F₀ rY rX a c ε
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let S := Functor.isoWhiskerRight (singleComplexOpenPullbackIso Y V).symm
      (derivedPullback (f ∣_ V)) ≪≫
    c (f ∣_ V) V.ι ≪≫
      eqToIso (congrArg (fun k ↦ derivedPullback k) (morphismRestrict_ι f V)) ≪≫
    (c (f ⁻¹ᵁ V).ι f).symm ≪≫
      Functor.isoWhiskerLeft (derivedPullback f)
        (singleComplexOpenPullbackIso X (f ⁻¹ᵁ V))
  have hc := singleComplexOpen_pinned_counit_unit f I
  dsimp only at hc
  have h := square_factorization (derivedPullback (f ∣_ V)) rY.mapDerivedCategory
    (derivedPullback f) rX.mapDerivedCategory S (F.rightDerivedFunctorUnit.app I)
    (rY.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I))
    ((a f).counit.app (DerivedCategory.Qh.obj I))
    ((ε f).app ((F.mapHomotopyCategory (.up ℤ)).obj I))
    (DerivedCategory.Qh.map
      (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
        |>.mapHomotopyCategory (.up ℤ)).counit.app I))
    (rX.mapDerivedCategoryFactorsh.hom.app I) hc
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  simpa only [S, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Iso.app_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.mapIso_hom,
    eqToIso.hom, eqToHom_app, Category.assoc, Functor.comp_obj,
    schemeDerivedDirectImage, RingedSpace.derivedModuleDirectImage, F] using h

end AlgebraicGeometry
