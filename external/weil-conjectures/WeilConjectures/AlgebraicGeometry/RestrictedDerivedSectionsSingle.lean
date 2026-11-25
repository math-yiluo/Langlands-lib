/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RestrictedDerivedSectionZeroComparison

/-! # Unshifted single comparison before restricted section homology

Source: Stacks Project, Tags 07A6 and 0D6F.
(blueprint: lem-sbc-restricted-derived-sections-single).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.RawRestrictedComparison

section SingleCompatibility

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma single_factor {C D : Type*}
    [Category C] [Category D]
    [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : C ⥤ D) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (X : C) :
    (L.mapDerivedCategorySingleFunctor 0).hom.app X =
      L.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X) ≫
        DerivedCategory.Q.map ((L.mapCochainComplexSingleFunctor 0).hom.app X) := by
  rw [← cancel_epi
    (L.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C 0).obj X))]
  simp only [Iso.inv_hom_id_app_assoc]
  exact L.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app X

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma complex_single_comp {C D E : Type*}
    [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    (L : C ⥤ D) (M : D ⥤ E)
    [L.Additive] [M.Additive] (X : C) :
    (M.mapHomologicalComplex (.up ℤ)).map ((L.mapCochainComplexSingleFunctor 0).hom.app X) ≫
        (M.mapCochainComplexSingleFunctor 0).hom.app (L.obj X) =
      (Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ M)) (.up ℤ)).hom.app
          ((CochainComplex.singleFunctor C 0).obj X) ≫
        ((L ⋙ M).mapCochainComplexSingleFunctor 0).hom.app X := by
  ext n
  by_cases hn : n = 0
  · subst n
    change M.map (𝟙 (L.obj X)) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    simp
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n hn).eq_of_tgt _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma derived_single_comp {C D E : Type*}
    [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (L : C ⥤ D) (M : D ⥤ E)
    [L.Additive] [M.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits M] [PreservesFiniteColimits M] (X : C) :
    (Functor.mapDerivedCategoryCompIso L M).inv.app
        ((DerivedCategory.singleFunctor C 0).obj X) ≫
      M.mapDerivedCategory.map ((L.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
        (M.mapDerivedCategorySingleFunctor 0).hom.app (L.obj X) =
      ((L ⋙ M).mapDerivedCategorySingleFunctor 0).hom.app X := by
  rw [single_factor L, single_factor M, single_factor (L ⋙ M)]
  simp only [Functor.map_comp, Category.assoc]
  erw [M.mapDerivedCategoryFactors_hom_naturality_assoc]
  rw [← DerivedCategory.Q.map_comp, complex_single_comp]
  simp only [Functor.map_comp]
  convert Functor.mapDerivedCategoryCompIso_fac_assoc L M
      ((CochainComplex.singleFunctor C 0).obj X)
      (DerivedCategory.Q.map (((L ⋙ M).mapCochainComplexSingleFunctor 0).hom.app X))
      using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma complex_single_nat {C D : Type*}
    [Category C] [Category D]
    [Abelian C] [Abelian D]
    {L M : C ⥤ D} [L.Additive] [M.Additive]
    (e : L ≅ M) (X : C) :
    (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
        ((CochainComplex.singleFunctor C 0).obj X) ≫
      (M.mapCochainComplexSingleFunctor 0).hom.app X =
    (L.mapCochainComplexSingleFunctor 0).hom.app X ≫
      (CochainComplex.singleFunctor D 0).map (e.hom.app X) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctor,
      HomologicalComplex.singleMapHomologicalComplex,
      HomologicalComplex.single, NatTrans.mapHomologicalComplex]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n hn).eq_of_tgt _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma derived_single_nat {C D : Type*}
    [Category C] [Category D]
    [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L M : C ⥤ D} [L.Additive] [M.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits M] [PreservesFiniteColimits M] (e : L ≅ M) (X : C) :
    (Functor.mapDerivedCategoryNatIso e).hom.app
        ((DerivedCategory.singleFunctor C 0).obj X) ≫
      (M.mapDerivedCategorySingleFunctor 0).hom.app X =
    (L.mapDerivedCategorySingleFunctor 0).hom.app X ≫
      (DerivedCategory.singleFunctor D 0).map (e.hom.app X) := by
  rw [single_factor L, single_factor M]
  erw [Functor.mapDerivedCategoryNatIso_fac_assoc]
  erw [← DerivedCategory.Q.map_comp, complex_single_nat, DerivedCategory.Q.map_comp]
  change _ ≫ _ ≫ _ = (_ ≫ _) ≫ _
  exact (Category.assoc _ _ _).symm

section Square

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma derived_single_square {C D E C' : Type*}
    [Category C] [Category D] [Category E] [Category C']
    [Abelian C] [Abelian D] [Abelian E] [Abelian C']
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory C']
    (L : C ⥤ D) (M : D ⥤ E)
    (A : C ⥤ C') (B : C' ⥤ E)
    [L.Additive] [M.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    [A.Additive] [B.Additive] [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [PreservesFiniteLimits B] [PreservesFiniteColimits B]
    (e : L ⋙ M ≅ A ⋙ B) (X : C) :
    (Functor.mapDerivedCategoryCompIso L M ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso A B).symm).hom.app
        ((DerivedCategory.singleFunctor C 0).obj X) ≫
      B.mapDerivedCategory.map ((A.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
        (B.mapDerivedCategorySingleFunctor 0).hom.app (A.obj X) =
      M.mapDerivedCategory.map ((L.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
        (M.mapDerivedCategorySingleFunctor 0).hom.app (L.obj X) ≫
          (DerivedCategory.singleFunctor E 0).map (e.hom.app X) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  erw [derived_single_comp A B X, derived_single_nat e X]
  rw [← derived_single_comp L M X]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma derived_single_square_coefficient {C D E C' : Type*}
    [Category C] [Category D] [Category E] [Category C']
    [Abelian C] [Abelian D] [Abelian E] [Abelian C']
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory C']
    (L : C ⥤ D) (M : D ⥤ E)
    (A : C ⥤ C') (B : C' ⥤ E)
    [L.Additive] [M.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    [A.Additive] [B.Additive] [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [PreservesFiniteLimits B] [PreservesFiniteColimits B]
    (e : L ⋙ M ≅ A ⋙ B) (X : C) (Y : C') (φ : A.obj X ⟶ Y) :
    (Functor.mapDerivedCategoryCompIso L M ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso A B).symm).hom.app
        ((DerivedCategory.singleFunctor C 0).obj X) ≫
      B.mapDerivedCategory.map ((A.mapDerivedCategorySingleFunctor 0).hom.app X ≫
        (DerivedCategory.singleFunctor C' 0).map φ) ≫
      (B.mapDerivedCategorySingleFunctor 0).hom.app Y =
      M.mapDerivedCategory.map ((L.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
        (M.mapDerivedCategorySingleFunctor 0).hom.app (L.obj X) ≫
          (DerivedCategory.singleFunctor E 0).map (e.hom.app X ≫ B.map φ) := by
  simp only [Functor.map_comp, Category.assoc]
  erw [(B.mapDerivedCategorySingleFunctor 0).hom.naturality φ]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun f ↦ f ≫ (DerivedCategory.singleFunctor E 0).map (B.map φ))
      (derived_single_square L M A B e X)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma single_sections {C D E C' : Type*}
    [Category C] [Category D] [Category E] [Category C']
    [Abelian C] [Abelian D] [Abelian E] [Abelian C']
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory C']
    {Z : Type*} [Category Z]
    (L : C ⥤ D) (M : D ⥤ E) (A : C ⥤ C') (B : C' ⥤ E)
    [L.Additive] [M.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    [A.Additive] [B.Additive] [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [PreservesFiniteLimits B] [PreservesFiniteColimits B]
    (e : L ⋙ M ≅ A ⋙ B) (T : DerivedCategory D ⥤ Z) (T' : DerivedCategory E ⥤ Z)
    (δ : T ⟶ M.mapDerivedCategory ⋙ T') (X : C) (Y : C') (φ : A.obj X ⟶ Y) :
    δ.app (L.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C 0).obj X)) ≫
      T'.map ((Functor.mapDerivedCategoryCompIso L M ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso A B).symm).hom.app
        ((DerivedCategory.singleFunctor C 0).obj X) ≫
        B.mapDerivedCategory.map ((A.mapDerivedCategorySingleFunctor 0).hom.app X ≫
          (DerivedCategory.singleFunctor C' 0).map φ) ≫
        (B.mapDerivedCategorySingleFunctor 0).hom.app Y) =
    T.map ((L.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      δ.app ((DerivedCategory.singleFunctor D 0).obj (L.obj X)) ≫
      T'.map (M.mapDerivedCategoryFactors.hom.app
        ((CochainComplex.singleFunctor D 0).obj (L.obj X)) ≫
        DerivedCategory.Q.map ((M.mapCochainComplexSingleFunctor 0).hom.app (L.obj X) ≫
          (CochainComplex.singleFunctor E 0).map (e.hom.app X ≫ B.map φ))) := by
  have hm : M.mapDerivedCategoryFactors.hom.app
      ((CochainComplex.singleFunctor D 0).obj (L.obj X)) ≫
      DerivedCategory.Q.map ((M.mapCochainComplexSingleFunctor 0).hom.app (L.obj X) ≫
        (CochainComplex.singleFunctor E 0).map (e.hom.app X ≫ B.map φ)) =
      (M.mapDerivedCategorySingleFunctor 0).hom.app (L.obj X) ≫
        (DerivedCategory.singleFunctor E 0).map (e.hom.app X ≫ B.map φ) := by
    rw [single_factor M]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  rw [hm, derived_single_square_coefficient L M A B e X Y φ]
  simp only [Functor.map_comp]
  exact (δ.naturality_assoc ((L.mapDerivedCategorySingleFunctor 0).hom.app X) _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma single_sections_expanded {C D E C' : Type*}
    [Category C] [Category D] [Category E] [Category C']
    [Abelian C] [Abelian D] [Abelian E] [Abelian C']
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory C']
    {Z : Type*} [Category Z]
    (L : C ⥤ D) (M : D ⥤ E) (A : C ⥤ C') (B : C' ⥤ E)
    [L.Additive] [M.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    [A.Additive] [B.Additive] [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [PreservesFiniteLimits B] [PreservesFiniteColimits B]
    (e : L ⋙ M ≅ A ⋙ B) (T : DerivedCategory D ⥤ Z) (T' : DerivedCategory E ⥤ Z)
    (δ : T ⟶ M.mapDerivedCategory ⋙ T') (X : C) (Y : C') (φ : A.obj X ⟶ Y) :
    (δ.app (L.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C 0).obj X)) ≫
      T'.map ((Functor.mapDerivedCategoryCompIso L M ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso A B).symm).hom.app
        ((DerivedCategory.singleFunctor C 0).obj X))) ≫
      T'.map (B.mapDerivedCategory.map ((A.mapDerivedCategorySingleFunctor 0).hom.app X ≫
          (DerivedCategory.singleFunctor C' 0).map φ)) ≫
      T'.map ((B.mapDerivedCategorySingleFunctor 0).hom.app Y) =
    T.map ((L.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      δ.app ((DerivedCategory.singleFunctor D 0).obj (L.obj X)) ≫
      T'.map (M.mapDerivedCategoryFactors.hom.app
        ((CochainComplex.singleFunctor D 0).obj (L.obj X)) ≫
        DerivedCategory.Q.map ((M.mapCochainComplexSingleFunctor 0).hom.app (L.obj X) ≫
          (CochainComplex.singleFunctor E 0).map (e.hom.app X ≫ B.map φ))) := by
  simpa only [Functor.map_comp, Category.assoc] using
    single_sections L M A B e T T' δ X Y φ

end Square

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma plus_single_map {C D : Type*}
    [Category C] [Category D]
    [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : C ⥤ D) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (X : C) (Y : D) (φ : L.obj X ⟶ Y) :
    DerivedCategory.Plus.ι.map ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app X ≫
        (DerivedCategory.Plus.singleFunctor D 0).map φ) =
      (L.mapDerivedCategorySingleFunctor 0).hom.app X ≫
        (DerivedCategory.singleFunctor D 0).map φ := by
  rw [Functor.map_comp, L.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app 0 X]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma evaluation_single {C D : Type*}
    [Category C] [Category D]
    [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : C ⥤ D) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [EnoughInjectives D] [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (R : D ⥤ AddCommGrpCat.{v + 1}) [R.Additive] [PreservesFiniteLimits R] (X : C) :
    (Evaluation.singleIso L R X).hom =
      R.rightDerivedFunctor.map ((L.mapDerivedCategorySingleFunctor 0).hom.app X) := by
  change R.rightDerivedFunctor.map
    (L.mapDerivedCategory.map (𝟙 _) ≫
      (L.mapDerivedCategorySingleFunctor 0).hom.app X ≫ 𝟙 _) = _
  simp

end SingleCompatibility

-- Restriction comparisons contain several large sheaf functors.
/-- On unshifted singles, the restriction and single comparisons give the explicit
complex pullback and coefficient map, before applying any homology functor.
Source: Stacks Project, Tags 07A6, 0D6F and 03Q8.
(blueprint: lem-sbc-restricted-derived-sections-single).

Proof: Factor the exact inverse-image single comparisons through localization Q.
Check compatibility with composition and natural isomorphisms on the actual single
complex: degree zero gives identities and the underived comparison, and every other
degree has zero target. Apply Q and its factorization laws to obtain the derived
square identity. Naturality of the single comparison incorporates the arbitrary
coefficient map. Apply derived global sections and move the source single comparison
past derivedSectionPullback by naturality; its unit and Leray construction need not
be expanded. The Plus inclusion identifies the bounded-below single comparison with
the same comparison in the full derived category. No coefficient is assumed
invertible; zero sheaves and empty schemes satisfy the same identities. No shift or
homology comparison is used. -/
theorem restrictedDerivedSections_single {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : (upperStar AddCommGrpCat.{v + 1} a).obj F ⟶ F') (U : S.Etale) :
    let q := rawAffineRestrictedMap a h h' w U
    let r := Limits.pullback.snd U.hom h
    let r' := Limits.pullback.snd U.hom h'
    let R := (upperStar AddCommGrpCat.{v + 1} r).obj F
    let τ := Functor.whiskerLeft
      (DerivedCategory.Plus.ι ⋙
        D(upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)))
      (derivedSectionPullback (rawAffineRestrictedMap a h h' w U)) ≫
    Functor.whiskerRight
      (Functor.whiskerLeft DerivedCategory.Plus.ι
        (derivedRestrictionIso a h h' w U).hom)
      (rightDerivedGlobalSections AddCommGrpCat.{v + 1} (Limits.pullback U.hom h'))
    τ.app ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      (sectionsFunctor ((MorphismProperty.Over.pullback @Etale ⊤ h').obj U)).map
        (((upperStar AddCommGrpCat.{v + 1} a).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
          (DerivedCategory.Plus.singleFunctor _ 0).map φ) ≫
      (Evaluation.singleIso (upperStar AddCommGrpCat.{v + 1} r')
        (Sheaf.Γ (Limits.pullback U.hom h').smallEtaleTopology AddCommGrpCat.{v + 1}) F').hom =
    (Evaluation.singleIso (upperStar AddCommGrpCat.{v + 1} r)
      (Sheaf.Γ (Limits.pullback U.hom h).smallEtaleTopology AddCommGrpCat.{v + 1}) F).hom ≫
      (derivedSectionPullback q).app
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj R)) ≫
      (rightDerivedGlobalSections AddCommGrpCat.{v + 1} (Limits.pullback U.hom h')).map
        ((upperStar AddCommGrpCat.{v + 1} q).mapDerivedCategoryFactors.hom.app
            ((CochainComplex.singleFunctor _ 0).obj R) ≫
          DerivedCategory.Q.map
            (((upperStar AddCommGrpCat.{v + 1} q).mapCochainComplexSingleFunctor 0).hom.app R ≫
              (CochainComplex.singleFunctor _ 0).map
                (rawAffineRestrictedCoefficient a h h' w F F' φ U))) := by
  dsimp only
  let L := upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)
  let M := upperStar AddCommGrpCat.{v + 1} (rawAffineRestrictedMap a h h' w U)
  let A := upperStar AddCommGrpCat.{v + 1} a
  let B := upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h')
  let T := (Sheaf.Γ (Limits.pullback U.hom h).smallEtaleTopology
    AddCommGrpCat.{v + 1}).rightDerivedFunctor
  let T' := (Sheaf.Γ (Limits.pullback U.hom h').smallEtaleTopology
    AddCommGrpCat.{v + 1}).rightDerivedFunctor
  let δ := derivedSectionPullback (rawAffineRestrictedMap a h h' w U)
  have hw : Limits.pullback.snd U.hom h' ≫ a =
      rawAffineRestrictedMap a h h' w U ≫ Limits.pullback.snd U.hom h := by
    simp [rawAffineRestrictedMap]
  let e : L ⋙ M ≅ A ⋙ B :=
    (upperStarComp AddCommGrpCat.{v + 1} (rawAffineRestrictedMap a h h' w U)
      (Limits.pullback.snd U.hom h)).symm ≪≫
    upperStarComp AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h') a
      (rawAffineRestrictedMap a h h' w U ≫ Limits.pullback.snd U.hom h) hw.symm
  rw [evaluation_single L
    (Sheaf.Γ (Limits.pullback U.hom h).smallEtaleTopology AddCommGrpCat.{v + 1}) F,
    evaluation_single B
      (Sheaf.Γ (Limits.pullback U.hom h').smallEtaleTopology AddCommGrpCat.{v + 1}) F']
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  change (δ.app (L.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj F)) ≫
    T'.map ((derivedRestrictionIso a h h' w U).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj F))) ≫
    T'.map (B.mapDerivedCategory.map (DerivedCategory.Plus.ι.map
      ((A.mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map φ))) ≫
    T'.map ((B.mapDerivedCategorySingleFunctor 0).hom.app F') =
    T.map ((L.mapDerivedCategorySingleFunctor 0).hom.app F) ≫
      δ.app ((DerivedCategory.singleFunctor _ 0).obj (L.obj F)) ≫
      T'.map (M.mapDerivedCategoryFactors.hom.app
        ((CochainComplex.singleFunctor _ 0).obj (L.obj F)) ≫
        DerivedCategory.Q.map ((M.mapCochainComplexSingleFunctor 0).hom.app (L.obj F) ≫
          (CochainComplex.singleFunctor _ 0).map
            (rawAffineRestrictedCoefficient a h h' w F F' φ U)))
  rw [plus_single_map A F F' φ]
  exact single_sections_expanded L M A B e T T' δ F F' φ

end AlgebraicGeometry.Etale.RawRestrictedComparison
