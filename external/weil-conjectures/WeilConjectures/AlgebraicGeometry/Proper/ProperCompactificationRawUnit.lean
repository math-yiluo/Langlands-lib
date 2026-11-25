/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphChosenComparisons
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationRawUnitComparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.Normalized.NormalizedDerivedUnitPasting

/-! # The raw unit for a proper compactification

## References

* Stacks Project, Tags 0F7I and 0D6E
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
attribute [local irreducible] lowerStar upperStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor rightDerivedLowerShriekIso

private theorem identity_open_inclusion
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) (𝟙 X)).app M ≫
        (lowerStarId (ModuleCat.{u + 1} A) X).hom.app M =
      (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
        (upperStarId (ModuleCat.{u + 1} A) X)).hom.app M := by
  let B := ModuleCat.{u + 1} A
  let a := openImmersionLowerShriekUpperStarAdjunction B (𝟙 X)
  let e := Adjunction.leftAdjointIdIso a (upperStarId B X)
  have he : a.unit.app M ≫ (upperStar B (𝟙 X)).map (e.hom.app M) =
      (upperStarId B X).inv.app M := by
    have h := unit_conjugateEquiv Adjunction.id a e.hom M
    simpa only [Adjunction.conjugateEquiv_leftAdjointIdIso_hom, e,
      Adjunction.id_unit, NatTrans.id_app, Functor.id_map, Functor.id_obj, Category.id_comp]
      using h.symm
  have hε : (upperStar B (𝟙 X)).map ((lowerStarId B X).hom.app M) ≫
      (upperStarId B X).hom.app M =
      (upperStarLowerStarAdjunction B (𝟙 X)).counit.app M := by
    erw [(upperStarId B X).hom.naturality]
    apply (cancel_epi ((upperStarId B X).inv.app ((lowerStar B (𝟙 X)).obj M))).1
    rw [Iso.inv_hom_id_app_assoc, upperStarId_inv_app_counit_app]
    rfl
  apply (a.homEquiv M M).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change a.unit.app M ≫ (upperStar B (𝟙 X)).map
      ((openImmersionLowerShriekToLowerStar B (𝟙 X)).app M ≫
        (lowerStarId B X).hom.app M) =
    a.unit.app M ≫ (upperStar B (𝟙 X)).map (e.hom.app M)
  rw [he]
  have hε' := ((upperStarId B X).app M).eq_comp_inv.mpr hε
  simp only [Functor.map_comp, hε']
  rw [reassoc_of% unit_map_openImmersionLowerShriekToLowerStar_app_counit B (𝟙 X) M]
  rfl

private theorem identity_mixed_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C]
    (O : C ⥤ C) (R : C ⥤ D) [O.Additive] [R.Additive]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    (e : O ≅ 𝟭 C) (J : HomotopyCategory C (.up ℤ)) :
    R.rightDerivedFunctorUnit.app J ≫ R.rightDerivedFunctor.map
        ((Functor.mapDerivedCategoryNatIso e ≪≫
          Functor.mapDerivedCategoryIdIso C).inv.app (DerivedCategory.Qh.obj J)) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory
            ((Functor.leftUnitor R).symm ≪≫ Functor.isoWhiskerRight e.symm R).hom
            (.up ℤ)).app J) ≫
        (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit O R).app J := by
  have hid : (Functor.mapDerivedCategoryIdIso C).inv.app (DerivedCategory.Qh.obj J) =
      (𝟭 C).mapDerivedCategoryFactorsh.inv.app J := by
    apply (cancel_mono ((Functor.mapDerivedCategoryIdIso C).hom.app
      (DerivedCategory.Qh.obj J))).1
    rw [Iso.inv_hom_id_app, Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj,
      Iso.inv_hom_id_app]
    rfl
  have he : (Functor.mapDerivedCategoryNatIso e ≪≫
      Functor.mapDerivedCategoryIdIso C).inv.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((e.inv.mapHomotopyCategory (.up ℤ)).app J) ≫
        O.mapDerivedCategoryFactorsh.inv.app J := by
    simp only [Iso.trans_inv, NatTrans.comp_app, hid]
    exact Functor.mapDerivedCategoryFactorsh_inv_app_mapDerivedCategoryNatIso_hom_app
      e.symm J
  rw [he, R.rightDerivedFunctor.map_comp]
  have hn := R.rightDerivedFunctorUnit.naturality
    ((e.inv.mapHomotopyCategory (.up ℤ)).app J)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  erw [← reassoc_of% hn]
  rw [Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app, comp_homotopy_inv]
  erw [DerivedCategory.Qh.map_id, Category.id_comp]
  congr 1
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective J
  apply congrArg DerivedCategory.Qh.map
  apply congrArg (HomotopyCategory.quotient D (.up ℤ)).map
  ext n
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, NatTrans.comp_app,
    Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Category.id_comp]

/-- The chosen proper comparison agrees with every normalized sheaf comparison after
precomposition with the raw right-derived unit. -/
theorem properCompactification_raw_unit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (q : X ⟶ Y) [IsProper q] [HasCompactification q]
    (c : Compactification q)
    (a : lowerStar (ModuleCat.{u + 1} A) q ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (ha : a ≫ compactificationSheafToDirectImage A c = 𝟙 _)
    (J : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    (lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctorUnit.app J ≫
        ((graphChosenProperComparison A q).symm ≪≫
          (rightDerivedLowerShriekIso A c).symm).hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).app J) ≫
        (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
          (lowerStar (ModuleCat.{u + 1} A) c.g)).app J := by
  let B := ModuleCat.{u + 1} A
  let c₀ := Compactification.ofIsProper q
  let O := openImmersionLowerShriek B (𝟙 X)
  let R := lowerStar B q
  let e := Adjunction.leftAdjointIdIso
    (openImmersionLowerShriekUpperStarAdjunction B (𝟙 X)) (upperStarId B X)
  let a₀ : R ≅ O ⋙ R := (Functor.leftUnitor R).symm ≪≫
    Functor.isoWhiskerRight e.symm R
  have h₀ : a₀.hom ≫ compactificationSheafToDirectImage A c₀ = 𝟙 R := by
    apply NatTrans.ext
    funext M
    change R.map (e.inv.app M) ≫
      R.map ((openImmersionLowerShriekToLowerStar B (𝟙 X)).app M) ≫
        (lowerStarComp B (𝟙 X) q q (Category.id_comp q).symm).hom.app M = 𝟙 _
    rw [lowerStarComp_id_left]
    simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
    erw [Category.comp_id]
    rw [← R.map_comp, ← R.map_comp, identity_open_inclusion A X M]
    change R.map (e.inv.app M ≫ e.hom.app M) = 𝟙 _
    rw [Iso.inv_hom_id_app, R.map_id]
  have hc := (unboundedEtaleCompactSupport_comparison_coherence A q).2
    c₀ c (HasCompactification.compactification q)
  have he : (rightDerivedLowerShriekIso A c₀).hom ≫
      (rightDerivedLowerShriekIso A c).inv =
      (rightDerivedLowerShriekOfCompactificationIso A c₀ c).hom := by
    apply (cancel_mono (rightDerivedLowerShriekIso A c).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simpa only [rightDerivedLowerShriekIso, Iso.trans_hom] using
      (congrArg Iso.hom hc).symm
  have ht := compactification_raw_unit_comparison A q R c₀ c a₀.hom a
    (h₀.trans ha.symm) J
  have hu := identity_mixed_unit O R e J
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← ht]
  simp only [graphChosenProperComparison, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerRight_inv, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, NatTrans.comp_app, Category.assoc]
  erw [Category.id_comp]
  change R.rightDerivedFunctorUnit.app J ≫ R.rightDerivedFunctor.map
      ((Functor.mapDerivedCategoryNatIso e ≪≫
        Functor.mapDerivedCategoryIdIso _).inv.app (DerivedCategory.Qh.obj J)) ≫
      (rightDerivedLowerShriekIso A c₀).hom.app (DerivedCategory.Qh.obj J) ≫
      (rightDerivedLowerShriekIso A c).inv.app (DerivedCategory.Qh.obj J) = _
  rw [reassoc_of% hu]
  have hk := congr_app he (DerivedCategory.Qh.obj J)
  simp only [NatTrans.comp_app] at hk
  erw [hk]
  rfl

end AlgebraicGeometry.Etale
