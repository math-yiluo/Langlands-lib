/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalScalarMateProjection
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullFlatModelMateNormalized
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullOrdinaryUnit
public import WeilConjectures.AlgebraicGeometry.NormalizedScalarRestrictionPush

/-! # Normalized scalar restriction and direct image

The comparison obtained by uniqueness of right adjoints is the geometric mate of the
canonical exact restriction/pullback comparison.

## References

* Stacks Project, Tags 0D6D, 0D6E and 07A6
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.Functor
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory AlgebraicGeometry.ProEtale.upperStarFromPoint

set_option allowUnsafeReducibility true
attribute [local reducible] Functor.mapHomotopyCategory L F
  CondensedRing.moduleObjectDerivedPullback
  CondensedRing.moduleObjectDerivedPushforward

private theorem ordinary_unit (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : HomotopyCategory (Modules Λ Y) (.up ℤ)) :
    (((CondensedRing.upperStar Λ f).mapHomotopyCategory (.up ℤ))).map
        (((Mod.extendRestrictAdjunction (coefficientMap a Y)).mapHomotopyCategory
            (.up ℤ)).unit.app H) ≫
      (NatTrans.mapHomotopyCategory (CondensedRing.comapUpperStarIso a f).inv (.up ℤ)).app
          (((extension a Y).mapHomotopyCategory (.up ℤ)).obj H) =
    ((Mod.extendRestrictAdjunction (coefficientMap a X)).mapHomotopyCategory
          (.up ℤ)).unit.app
        (((CondensedRing.upperStar Λ f).mapHomotopyCategory (.up ℤ)).obj H) ≫
      ((V₀ a X).mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory (CondensedRing.pullIso a f).hom (.up ℤ)).app H) := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  simp only [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Functor.mapHomotopyCategory_map, NatTrans.mapHomotopyCategory_app]
  have hx := Adjunction.mapHomotopyCategory_unit_app_quotient (.up ℤ)
    (Mod.extendRestrictAdjunction (coefficientMap a X))
    (((CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj P)
  erw [hx]
  simp only [← Functor.map_comp]
  congr 1
  ext i : 1
  exact AlgebraicGeometry.ProEtale.ordinaryScalarUnit a f (P.X i)

private theorem scalar_unit_fac (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (H : HomotopyCategory (Modules Λ T) (.up ℤ)) :
    (scalarAdj a T).unit.app (DerivedCategory.Qh.obj H) ≫
      (V a T).map ((scalarCounit a T).app H) ≫
      (V₀ a T).mapDerivedCategoryFactorsh.hom.app
        (((extension a T).mapHomotopyCategory (.up ℤ)).obj H) =
    DerivedCategory.Qh.map
      (((Mod.extendRestrictAdjunction (coefficientMap a T)).mapHomotopyCategory
        (.up ℤ)).unit.app H) := by
  unfold scalarAdj scalarCounit D Mod.derivedExtendMapDerivedCategoryAdjunction
  dsimp only [id]
  exact mixedDerivedUnitFac (Mod.extendRestrictAdjunction (coefficientMap a T)) H

private theorem restriction_pull_fac (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : HomotopyCategory (Modules Λ' Y) (.up ℤ)) :
    (scalarRestrictionPull a f).inv.app (DerivedCategory.Qh.obj N) ≫
      (V a X).map ((pullCounit (Λ := Λ') f).app N) ≫
      (V₀ a X).mapDerivedCategoryFactorsh.hom.app
        (((CondensedRing.upperStar Λ' f).mapHomotopyCategory (.up ℤ)).obj N) =
    (L Λ f).map ((V₀ a Y).mapDerivedCategoryFactorsh.hom.app N) ≫
      (pullCounit (Λ := Λ) f).app (((V₀ a Y).mapHomotopyCategory (.up ℤ)).obj N) ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory (CondensedRing.comapUpperStarIso a f).inv
          (.up ℤ)).app N) := by
  unfold scalarRestrictionPull pullCounit L CondensedRing.moduleObjectDerivedPullback
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
  dsimp only [id]
  have h := exactLeftSquareFac (V₀ a Y) (CondensedRing.upperStar Λ f)
    (CondensedRing.upperStar Λ' f) (V₀ a X) (CondensedRing.comapUpperStarIso a f) N
  simpa only [CondensedRing.derivedComapUpperStarIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using h

private theorem scalar_mate_fac (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory (Modules Λ Y) (.up ℤ)) :
    (D a X).map ((pullCounit (Λ := Λ) f).app P) ≫
        (scalarCounit a X).app
          (((CondensedRing.upperStar Λ f).mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (CondensedRing.pullIso a f).hom (.up ℤ)).app P) =
      (((mateEquiv (scalarAdj a Y) (scalarAdj a X)).symm
        (TwoSquare.mk _ _ _ _ (scalarRestrictionPull a f).inv))).app
          (DerivedCategory.Qh.obj P) ≫
        (L Λ' f).map ((scalarCounit a Y).app P) ≫
        (pullCounit (Λ := Λ') f).app
          (((extension a Y).mapHomotopyCategory (.up ℤ)).obj P) := by
  let FP := ((CondensedRing.upperStar Λ f).mapHomotopyCategory (.up ℤ)).obj P
  let TP := ((extension a Y).mapHomotopyCategory (.up ℤ)).obj P
  let ph := (NatTrans.mapHomotopyCategory (CondensedRing.pullIso a f).hom (.up ℤ)).app P
  let qh := (NatTrans.mapHomotopyCategory (CondensedRing.comapUpperStarIso a f).inv
    (.up ℤ)).app TP
  let ηX := ((Mod.extendRestrictAdjunction (coefficientMap a X)).mapHomotopyCategory
    (.up ℤ)).unit.app FP
  let ηY := ((Mod.extendRestrictAdjunction (coefficientMap a Y)).mapHomotopyCategory
    (.up ℤ)).unit.app P
  have hOrd := naturalOrdinaryFac (pullCounit (Λ := Λ) f) ηY ηX
    (((V₀ a X).mapHomotopyCategory (.up ℤ)).map ph) qh (ordinary_unit a f P)
  have ho := (V₀ a X).mapDerivedCategoryFactorsh.hom.naturality ph
  dsimp only [Functor.comp_map] at ho
  exact mateModel (scalarAdj a X) (scalarAdj a Y) (L Λ f) (L Λ' f)
    (scalarRestrictionPull a f).inv
    ((pullCounit (Λ := Λ) f).app P) ((scalarCounit a X).app FP)
    (DerivedCategory.Qh.map ph) ((scalarCounit a Y).app P)
    ((pullCounit (Λ := Λ') f).app TP)
    ((V₀ a X).mapDerivedCategoryFactorsh.hom.app _)
    ((V₀ a X).mapDerivedCategoryFactorsh.hom.app _)
    ((V₀ a Y).mapDerivedCategoryFactorsh.hom.app TP)
    ((pullCounit (Λ := Λ) f).app _) (DerivedCategory.Qh.map qh)
    (DerivedCategory.Qh.map ηX) (DerivedCategory.Qh.map ηY)
    (DerivedCategory.Qh.map (((V₀ a X).mapHomotopyCategory (.up ℤ)).map ph))
    (scalar_unit_fac a X FP) (scalar_unit_fac a Y P) ho (restriction_pull_fac a f TP) hOrd

private def comparisonCounit (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.Qh ⋙ (D a Y ⋙ L Λ' f) ⟶
      (extension a Y ⋙ CondensedRing.upperStar Λ' f).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (scalarCounit a Y) (L Λ' f) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((extension a Y).mapHomotopyCategory (.up ℤ))
      (pullCounit (Λ := Λ') f) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (extension a Y ⋙ CondensedRing.upperStar Λ' f)) (.up ℤ)).hom
      DerivedCategory.Qh

private theorem comparisonCounit_app (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory (Modules Λ Y) (.up ℤ)) :
    (comparisonCounit a f).app P =
      (L Λ' f).map ((scalarCounit a Y).app P) ≫
        (pullCounit (Λ := Λ') f).app
          (((extension a Y).mapHomotopyCategory (.up ℤ)).obj P) := by
  simp only [comparisonCounit, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem comparisonCounit_derived (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (D a Y ⋙ L Λ' f).IsLeftDerivedFunctor (comparisonCounit a f)
      (HomotopyCategory.quasiIso (Modules Λ Y) (.up ℤ)) := by
  have : (extension a Y ⋙ CondensedRing.upperStar Λ' f).PreservesKFlatQuasiIso := {
    quasiIso_map hK hL q _ := by
      have := (extension a Y).quasiIso_mapHomologicalComplex_map_of_kFlat hK hL q
      exact inferInstanceAs (QuasiIso
        (((CondensedRing.upperStar Λ' f).mapHomologicalComplex (.up ℤ)).map
          (((extension a Y).mapHomologicalComplex (.up ℤ)).map q))) }
  apply (Functor.isLeftDerivedFunctor_iff_isIso_app_of_kFlat
    (extension a Y ⋙ CondensedRing.upperStar Λ' f) (comparisonCounit a f)).2
  intro P hP
  rw [comparisonCounit_app]
  have hs : IsIso ((scalarCounit a Y).app
      ((HomotopyCategory.quotient _ _).obj P)) := by
    unfold scalarCounit D
    dsimp only [id]
    exact (extension a Y).isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  have hg : IsIso ((pullCounit (Λ := Λ') f).app
      (((extension a Y).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P))) := by
    unfold pullCounit
    dsimp only [id]
    infer_instance
  exact IsIso.comp_isIso' (Functor.map_isIso _ _) hg

private theorem map_comp_iso_eq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {I : C ⥤ D}
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (e : F ⋙ G ≅ H ⋙ I) (P : HomotopyCategory A (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app P =
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  rfl

private theorem inverse_normalization
    {C : Type*} [Category C] {X Y Z W : C} (b : X ≅ Y)
    (A : Y ⟶ Z) (B : X ⟶ W) (s : W ⟶ Z) (t : Z ⟶ W)
    (h : b.hom ≫ A = B ≫ s) (hst : s ≫ t = 𝟙 _) :
    b.inv ≫ B = A ≫ t := by
  rw [← cancel_epi b.hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, h, Category.assoc, hst, Category.comp_id]

private theorem rightUniq_conjugate
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (a' : L' ⊣ R') (e : L ≅ L') :
    (a.rightAdjointUniq (a'.ofNatIsoLeft e.symm)).hom =
      conjugateEquiv a a' e.inv := by
  ext X
  simp [Adjunction.rightAdjointUniq, conjugateEquiv_apply_app,
    Adjunction.ofNatIsoLeft_unit]

private theorem normalized_inverse (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) (hb : PullNormalized a f b) :
    b.inv = ((mateEquiv (scalarAdj a Y) (scalarAdj a X)).symm
      (TwoSquare.mk _ _ _ _ (scalarRestrictionPull a f).inv)) := by
  have := comparisonCounit_derived a f
  apply Functor.leftDerived_ext _ (comparisonCounit a f)
    (HomotopyCategory.quasiIso (Modules Λ Y) (.up ℤ)) _
  ext H
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  let H := (HomotopyCategory.quotient (Modules Λ Y) (.up ℤ)).obj P
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, comparisonCounit_app]
  rw [← scalar_mate_fac a f H]
  have h := hb H
  simp only [mapHomotopyCategoryCompIso_refl_hom_app, map_comp_iso_eq,
    Iso.symm_hom] at h
  erw [DerivedCategory.Qh.map_id, Category.comp_id] at h
  have hs :
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
        (CondensedRing.pullIso a f).inv (.up ℤ)).app H) ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
        (CondensedRing.pullIso a f).hom (.up ℤ)).app H) = 𝟙 _ := by
    rw [← DerivedCategory.Qh.map_comp, ← NatTrans.comp_app,
      ← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
      NatTrans.mapHomotopyCategory_id, NatTrans.id_app, CategoryTheory.Functor.map_id]
  have hi := inverse_normalization
    (b.app (DerivedCategory.Qh.obj H))
    ((D a X).map ((pullCounit (Λ := Λ) f).app H) ≫
      (scalarCounit a X).app
        (((CondensedRing.upperStar Λ f).mapHomotopyCategory (.up ℤ)).obj H))
    ((L Λ' f).map ((scalarCounit a Y).app H) ≫
      (pullCounit (Λ := Λ') f).app (((extension a Y).mapHomotopyCategory (.up ℤ)).obj H))
    (DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
      (CondensedRing.pullIso a f).inv (.up ℤ)).app H))
    (DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
      (CondensedRing.pullIso a f).hom (.up ℤ)).app H))
    (by
      convert h using 1 <;> first | rfl | exact Category.assoc _ _ _) hs
  simp only [Category.assoc] at hi
  convert hi using 1
  rfl

/-- Normalizing scalar extension against the ordinary balancing map identifies the
right-adjoint-uniqueness comparison with the geometric mate of exact scalar restriction. -/
theorem normalized_scalar_restriction_push
    (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
    (hb : PullNormalized a f b) :
    (restrictPush a f b).hom = scalarRestrictionPush a f := by
  have h := normalized_inverse a f b hb
  have hq : (mateEquiv (scalarAdj a Y) (scalarAdj a X)
      (TwoSquare.mk _ _ _ _ b.inv)) = (scalarRestrictionPull a f).inv := by
    rw [h]
    change (mateEquiv (scalarAdj a Y) (scalarAdj a X)
      ((mateEquiv (scalarAdj a Y) (scalarAdj a X)).symm
        (TwoSquare.mk _ _ _ _ (scalarRestrictionPull a f).inv))) = _
    rw [Equiv.apply_symm_apply]
  have hi := iterated_mateEquiv_conjugateEquiv
    (scalarAdj a Y) (scalarAdj a X) (adj Λ f) (adj Λ' f)
    (TwoSquare.mk _ _ _ _ b.inv)
  have hsq : mateEquiv (scalarAdj a Y) (scalarAdj a X)
      (TwoSquare.mk _ _ _ _ b.inv) =
      TwoSquare.mk _ _ _ _ (scalarRestrictionPull a f).inv := by
    ext K
    exact congr_app hq K
  rw [hsq] at hi
  rw [restrictPush, rightUniq_conjugate]
  exact hi.symm

end AlgebraicGeometry.ProEtale.QuotientChange
