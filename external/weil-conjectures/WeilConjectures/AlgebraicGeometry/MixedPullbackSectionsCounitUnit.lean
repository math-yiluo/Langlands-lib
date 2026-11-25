/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MixedAffineSectionsComplexUnit
public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Sections of the pullback counit and the normalized Leray unit
Source: Stacks Project, Tags 079W and 0D5T.
(blueprint: lem-sc-mixed-pullback-sections-counit-unit).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wA
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem mixedSections_homEquiv_unit
    {C₀ D₀ C D : Type*} [Category C₀] [Category D₀] [Category C] [Category D]
    {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀} {L : C ⥤ D} {R : D ⥤ C}
    (adj₀ : L₀ ⊣ R₀) (adj : L ⊣ R) (Q : C₀ ⥤ C) (Q' : D₀ ⥤ D) (M : C₀)
    (ε : L.obj (Q.obj M) ⟶ Q'.obj (L₀.obj M))
    (β : Q.obj (R₀.obj (L₀.obj M)) ⟶ R.obj (Q'.obj (L₀.obj M)))
    (h : adj.homEquiv _ _ (ε ≫ Q'.map (𝟙 _)) =
      Q.map (adj₀.homEquiv _ _ (𝟙 _)) ≫ β) :
    adj.unit.app (Q.obj M) ≫ R.map ε = Q.map (adj₀.unit.app M) ≫ β := by
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Adjunction.homEquiv_id,
    Adjunction.homEquiv_unit] at h
  exact h

private theorem mixedSections_mapHomotopyCategory_unit
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive D]
    [(HomotopyCategory.quotient A (.up ℤ)).IsLocalization
      (HomologicalComplex.homotopyEquivalences A (.up ℤ))]
    [(HomotopyCategory.quotient B (.up ℤ)).IsLocalization
      (HomologicalComplex.homotopyEquivalences B (.up ℤ))]
    (K : A ⥤ B) (F : B ⥤ A) (H : A ⥤ D) [K.Additive] [F.Additive] [H.Additive]
    (adj : K ⊣ F) (C : CochainComplex A ℤ) :
    (H.mapHomotopyCategory (.up ℤ)).map
        ((adj.mapHomotopyCategory (.up ℤ)).unit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj C)) =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        (((Functor.whiskerRight adj.unit H).mapHomologicalComplex (.up ℤ)).app C) := by
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient, Functor.mapHomotopyCategory_map]
  rfl

private theorem mixedSections_unit_naturality
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
    (Q : A ⥤ B) (H₀ : A ⥤ D) (H : B ⥤ D) (F : C ⥤ B) (J : C ⥤ E) (R : E ⥤ D)
    (s : H₀ ⟶ Q ⋙ H) (L : F ⋙ H ≅ J ⋙ R)
    {M M' : A} {X Y : C} (a : M ⟶ M') (ε : X ⟶ Y)
    (η : Q.obj M ⟶ F.obj X) (β : Q.obj M' ⟶ F.obj Y)
    (u : H₀.obj M' ⟶ R.obj (J.obj Y))
    (hunit : η ≫ F.map ε = Q.map a ≫ β)
    (hL : s.app M' ≫ H.map β ≫ L.hom.app Y = u) :
    s.app M ≫ H.map η ≫ L.hom.app X ≫ R.map (J.map ε) = H₀.map a ≫ u := by
  erw [← L.hom.naturality ε]
  change s.app M ≫ H.map η ≫ H.map (F.map ε) ≫ L.hom.app Y = _
  rw [← Functor.map_comp_assoc, hunit, Functor.map_comp]
  simp only [Category.assoc]
  erw [← s.naturality_assoc a]
  rw [hL]

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

-- Both localization factor isomorphisms have identity components on complexes.
private theorem sectionsComplexUnit_eq (S : Scheme.{u})
    (C : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ) :
    mixedSectionsComplexUnit S C =
      (RingedSpace.globalSectionsFunctor S.toRingedSpace).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj C) := by
  simp only [mixedSectionsComplexUnit, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.id_comp, Category.comp_id]

private theorem mixedSections_leray_unit {S T : Scheme.{u}} (g : T ⟶ S)
    [(RingedSpace.globalSectionsFunctor S.toRingedSpace).Additive]
    [(RingedSpace.globalSectionsFunctor T.toRingedSpace).Additive]
    (N : HomotopyCategory (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (.up ℤ)) :
    let H := RingedSpace.globalSectionsFunctor S.toRingedSpace
    let J := RingedSpace.globalSectionsFunctor T.toRingedSpace
    let F := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let R := ModuleCat.restrictScalars.{u} g.appTop.hom
    let s := H.rightDerivedFunctorUnit
    let t := J.rightDerivedFunctorUnit
    let β := F.rightDerivedFunctorUnit
    let L := mixedGlobalSectionsDirectImageIso g
    s.app ((F.mapHomotopyCategory (.up ℤ)).obj N) ≫
        (schemeDerivedGlobalSections S).map (β.app N) ≫ L.hom.app _ =
      R.mapDerivedCategoryFactorsh.inv.app ((J.mapHomotopyCategory (.up ℤ)).obj N) ≫
        (schemeGlobalScalarRestriction g).map (t.app N) := by
  intro H J F R s t β L
  let c₀ := Classical.choose (exists_mixedGlobalSectionsDirectImageIso g)
  have hc := Classical.choose_spec
    (Classical.choose_spec (exists_mixedGlobalSectionsDirectImageIso g))
  have hc₀ : c₀ = Iso.refl (F ⋙ H) := by
    apply Iso.ext
    ext A x
    exact hc.1 A x
  have hL := hc.2 N
  change s.app ((F.mapHomotopyCategory (.up ℤ)).obj N) ≫
      (schemeDerivedGlobalSections S).map (β.app N) ≫ L.hom.app _ = _ at hL
  rw [show Classical.choose (exists_mixedGlobalSectionsDirectImageIso g) =
      Iso.refl (F ⋙ H) from hc₀] at hL
  change _ = DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ H)) (.up ℤ)).hom.app N ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ H)) (.up ℤ)).inv.app N) ≫
      R.mapDerivedCategoryFactorsh.inv.app ((J.mapHomotopyCategory (.up ℤ)).obj N) ≫
      (schemeGlobalScalarRestriction g).map (t.app N) at hL
  rw [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp] at hL
  exact hL

omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private theorem normalizationRestriction_factors_inv
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (E : CochainComplex (ModuleCat.{u} B) ℤ) :
    let R := ModuleCat.restrictScalars.{u} f
    R.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ (.up ℤ)).obj E) =
      R.mapDerivedCategoryFactors.inv.app E := by
  intro R
  have hfac := R.mapDerivedCategoryFactorsh_hom_app E
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv] at hfac
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, Category.comp_id] at hfac
  have hR : R.mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj E) =
      R.mapDerivedCategoryFactors.inv.app E := by
    apply (cancel_mono (R.mapDerivedCategoryFactors.hom.app E)).1
    erw [← hfac]
    erw [Iso.inv_hom_id_app]
    erw [hfac, Iso.inv_hom_id_app]
    rfl
  exact hR

/-- Apply sections to a pullback counit satisfying the underived unit factorization.
Source: Stacks Project, Tags 079W (derived adjunction) and 0D5T (Leray composition).
(blueprint: lem-sc-mixed-pullback-sections-counit-unit).

Proof: On the homotopy category write alpha for the ordinary pullback adjunction unit,
 beta for the right-derived direct-image unit, and s for the sections right-derived unit.
The hypothesis says eta followed by derived direct image of epsilon equals Q(alpha);beta.
Apply derived S-sections. Naturality of s at alpha moves Q(alpha) to ordinary sections.
Naturality of the normalized Leray isomorphism at epsilon moves sections of epsilon
across that isomorphism. Its defining unit equation then replaces s;sections(beta);Leray
by the ordinary direct-image/sections comparison followed by exact scalar restriction's
localization factor and restriction of the T-sections unit. The underived comparison is
identity on sections, so the ordinary map is precisely sections of alpha. Finally
conjugate by quotientCompQhIso and mapHomotopyCategoryFactors at C and g-star C.
Naturality of these factors identifies this conjugated ordinary map with Q(d_C), and
mapDerivedCategoryFactorsh with mapDerivedCategoryFactors. This proves the displayed
identity. No counit invertibility, affine hypothesis, K-flatness, boundedness or equality
between w and wA is needed; zero complexes and empty schemes obey the same naturalities. -/
theorem mixedPullback_sections_counit_unit {S T : Scheme.{u}} (g : T ⟶ S)
    [(Scheme.Modules.tensorPullback g).Additive]
    [(RingedSpace.globalSectionsFunctor S.toRingedSpace).Additive]
    [(RingedSpace.globalSectionsFunctor T.toRingedSpace).Additive]
    (C : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    (ε : DerivedCategory.Qh ⋙ derivedPullback.{u, w} g ⟶
      (Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh
          (C := SheafOfModules.{u} (moduleRings T.toRingedSpace)))
    (hunit :
      (schemeHomPullbackAdjunction.{u, w} g).homEquiv
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj C))
          ((DerivedCategory.Qh
            (C := SheafOfModules.{u} (moduleRings T.toRingedSpace))).obj
            (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient _ (.up ℤ)).obj C)))
          (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj C) ≫
            (DerivedCategory.Qh
              (C := SheafOfModules.{u} (moduleRings T.toRingedSpace))).map (𝟙 _)) =
      (DerivedCategory.Qh
        (C := SheafOfModules.{u} (moduleRings S.toRingedSpace))).map
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).mapHomotopyCategory
          (.up ℤ)).homEquiv ((HomotopyCategory.quotient _ (.up ℤ)).obj C) _ (𝟙 _)) ≫
        (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj C))) :
    let H := RingedSpace.globalSectionsFunctor S.toRingedSpace
    let J := RingedSpace.globalSectionsFunctor T.toRingedSpace
    let K : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings T.toRingedSpace) := Scheme.Modules.tensorPullback g
    let R := ModuleCat.restrictScalars.{u} g.appTop.hom
    let d : H ⟶ K ⋙ J ⋙ R := Functor.whiskerRight
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit H
    let D := (K.mapHomologicalComplex (.up ℤ)).obj C
    let e : (derivedPullback.{u, w} g).obj (DerivedCategory.Q.obj C) ⟶ DerivedCategory.Q.obj D :=
      (derivedPullback.{u, w} g).map ((DerivedCategory.quotientCompQhIso _).inv.app C) ≫
        ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj C) ≫
        (DerivedCategory.Qh
          (C := SheafOfModules.{u} (moduleRings T.toRingedSpace))).map
          ((K.mapHomotopyCategoryFactors (.up ℤ)).hom.app C) ≫
        (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (moduleRings T.toRingedSpace))).hom.app D
    mixedSectionsComplexUnit S C ≫
      (schemeDerivedGlobalSections S).map
        ((schemeHomPullbackAdjunction.{u, w} g).unit.app (DerivedCategory.Q.obj C)) ≫
      (mixedGlobalSectionsDirectImageIso g).hom.app
        ((derivedPullback.{u, w} g).obj (DerivedCategory.Q.obj C)) ≫
      (schemeGlobalScalarRestriction g).map ((schemeDerivedGlobalSections T).map e) =
    DerivedCategory.Q.map ((d.mapHomologicalComplex (.up ℤ)).app C) ≫
      R.mapDerivedCategoryFactors.inv.app ((J.mapHomologicalComplex (.up ℤ)).obj D) ≫
      (schemeGlobalScalarRestriction g).map (mixedSectionsComplexUnit T D) := by
  intro H J K R d D e
  let F := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
  have : H.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive H
  have : J.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive J
  have : K.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive K
  have : R.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive R
  have : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  let M := (HomotopyCategory.quotient _ (.up ℤ)).obj C
  let N := (K.mapHomotopyCategory (.up ℤ)).obj M
  let adj : K ⊣ F := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let a : M ⟶ (F.mapHomotopyCategory (.up ℤ)).obj N :=
    (adj.mapHomotopyCategory (.up ℤ)).unit.app M
  let s := H.rightDerivedFunctorUnit
  let t := J.rightDerivedFunctorUnit
  let β := F.rightDerivedFunctorUnit
  let η := (schemeHomPullbackAdjunction.{u, w} g).unit
  let L := mixedGlobalSectionsDirectImageIso g
  let E := (J.mapHomologicalComplex (.up ℤ)).obj D
  have he : e = ε.app M := by
    change (derivedPullback.{u, w} g).map (𝟙 (DerivedCategory.Q.obj C)) ≫
      ε.app M ≫ DerivedCategory.Qh.map (𝟙 N) ≫ 𝟙 (DerivedCategory.Q.obj D) = _
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id, Category.comp_id]
  erw [sectionsComplexUnit_eq, sectionsComplexUnit_eq]
  rw [he]
  have hL := mixedSections_leray_unit g N
  have hu := mixedSections_homEquiv_unit (adj.mapHomotopyCategory (.up ℤ))
    (schemeHomPullbackAdjunction g) DerivedCategory.Qh DerivedCategory.Qh M
    (ε.app M) (β.app N) hunit
  have hh := mixedSections_unit_naturality DerivedCategory.Qh
    (H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (schemeDerivedGlobalSections S) (schemeDerivedDirectImage g)
    (schemeDerivedGlobalSections T) (schemeGlobalScalarRestriction g)
    s L a (ε.app M) (η.app (DerivedCategory.Qh.obj M)) (β.app N) _ hu hL
  dsimp only [Functor.comp_map] at hh
  have ha := mixedSections_mapHomotopyCategory_unit K F H adj C
  have hR := normalizationRestriction_factors_inv g.appTop.hom E
  erw [ha, hR] at hh
  exact hh

end AlgebraicGeometry
