/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison

public import WeilConjectures.AlgebraicGeometry.AffinePullbackModelComparisonsIsIso

/-! # Pullback unit on affine sections models

Source: Stacks Project, perfect.tex, Tags 06Z0, 08DV, 08DW and 0AA7.
(blueprint: new-affine-pullback-sections-model-unit).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry

private theorem compUnit_app
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (H : C ⥤ D) (G : D ⥤ E) [H.Additive] [G.Additive]
    (J : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit H G).app J =
      G.rightDerivedFunctorUnit.app ((H.mapHomotopyCategory (.up ℤ)).obj J) ≫
        G.rightDerivedFunctor.map (H.rightDerivedFunctorUnit.app J) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective J
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]
  have hc : (Functor.mapHomotopyCategoryCompIso (Iso.refl (H ⋙ G)) (.up ℤ)).inv.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj K) = 𝟙 _ := by
    change (HomotopyCategory.quotient E (.up ℤ)).map (𝟙 _) = 𝟙 _
    exact CategoryTheory.Functor.map_id _ _
  erw [hc, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem normalizedCompUnit_app
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (H : C ⥤ D) (G : D ⥤ E) [H.Additive] [G.Additive]
    {DG : DerivedCategory D ⥤ DerivedCategory E} (a : G.rightDerivedFunctor ≅ DG)
    (J : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit H G).app J ≫
        a.hom.app (H.rightDerivedFunctor.obj (DerivedCategory.Qh.obj J)) =
      G.rightDerivedFunctorUnit.app ((H.mapHomotopyCategory (.up ℤ)).obj J) ≫
        a.hom.app (DerivedCategory.Qh.obj ((H.mapHomotopyCategory (.up ℤ)).obj J)) ≫
          DG.map (H.rightDerivedFunctorUnit.app J) := by
  erw [compUnit_app, Category.assoc, a.hom.naturality]

-- Exact restriction expands the right-derived uniqueness comparison.
private theorem exactCompUnit_fac
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (H : C ⥤ D) (G : D ⥤ E) [H.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {DH : DerivedCategory C ⥤ DerivedCategory D} (a : H.rightDerivedFunctor ≅ DH)
    (J : HomotopyCategory C (.up ℤ)) :
    (H ⋙ G).rightDerivedFunctorUnit.app J ≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso H G ≪≫
        Functor.isoWhiskerRight a G.mapDerivedCategory).hom.app (DerivedCategory.Qh.obj J) =
    G.mapDerivedCategoryFactorsh.inv.app ((H.mapHomotopyCategory (.up ℤ)).obj J) ≫
      G.mapDerivedCategory.map (H.rightDerivedFunctorUnit.app J ≫
        a.hom.app (DerivedCategory.Qh.obj J)) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, ← Category.assoc]
  erw [Functor.rightDerivedFunctorCompMapDerivedCategoryIso_hom_fac,
    Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app']
  rw [Functor.map_comp, Category.assoc]

private theorem homotopy_unit_pasting
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    [Abelian.HasKInjectiveResolutions F]
    (P : C ⥤ D) (H : D ⥤ C) (A : C ⥤ E) (B : D ⥤ F) (U : F ⥤ E)
    [P.Additive] [H.Additive] [A.Additive] [B.Additive] [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {LP : DerivedCategory C ⥤ DerivedCategory D}
    {DA : DerivedCategory C ⥤ DerivedCategory E}
    {DB : DerivedCategory D ⥤ DerivedCategory F}
    (a : A.rightDerivedFunctor ≅ DA) (b : B.rightDerivedFunctor ≅ DB)
    (v : H ⋙ A ≅ B ⋙ U) (r : H.rightDerivedFunctor ⋙ DA ≅ DB ⋙ U.mapDerivedCategory)
    (hr : ∀ J : HomotopyCategory D (.up ℤ),
      (Functor.rightDerivedFunctorCompUnit H A).app J ≫
        a.hom.app (H.rightDerivedFunctor.obj (DerivedCategory.Qh.obj J)) ≫
        r.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((v.hom.mapHomotopyCategory (.up ℤ)).app J) ≫
        (B ⋙ U).rightDerivedFunctorUnit.app J ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso B U ≪≫
          Functor.isoWhiskerRight b U.mapDerivedCategory).hom.app (DerivedCategory.Qh.obj J))
    (η : 𝟭 _ ⟶ LP ⋙ H.rightDerivedFunctor)
    (ε : DerivedCategory.Qh ⋙ LP ⟶ P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (K : CochainComplex C ℤ)
    (e : K ⟶ (H.mapHomologicalComplex (.up ℤ)).obj
      ((P.mapHomologicalComplex (.up ℤ)).obj K))
    (hη : η.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj K)) ≫
      H.rightDerivedFunctor.map (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj K)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map e) ≫
        H.rightDerivedFunctorUnit.app ((P.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient C (.up ℤ)).obj K))) :
    A.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫ a.hom.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj K)) ≫
        DA.map (η.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj K))) ≫
        r.hom.app (LP.obj (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj K))) ≫
        U.mapDerivedCategory.map (DB.map (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj K))) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient E (.up ℤ)).map
        ((A.mapHomologicalComplex (.up ℤ)).map e ≫
          (v.hom.mapHomologicalComplex (.up ℤ)).app
            ((P.mapHomologicalComplex (.up ℤ)).obj K))) ≫
        U.mapDerivedCategoryFactorsh.inv.app
          ((B.mapHomotopyCategory (.up ℤ)).obj ((P.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient C (.up ℤ)).obj K))) ≫
        U.mapDerivedCategory.map
          (B.rightDerivedFunctorUnit.app ((P.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient C (.up ℤ)).obj K)) ≫
            b.hom.app (DerivedCategory.Qh.obj ((P.mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient C (.up ℤ)).obj K)))) := by
  have hn := r.hom.naturality (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj K))
  have ha := a.hom.naturality (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map e))
  have hu := A.rightDerivedFunctorUnit.naturality ((HomotopyCategory.quotient C (.up ℤ)).map e)
  have hc := normalizedCompUnit_app H A a ((P.mapHomotopyCategory (.up ℤ)).obj
    ((HomotopyCategory.quotient C (.up ℤ)).obj K))
  have he := exactCompUnit_fac B U b ((P.mapHomotopyCategory (.up ℤ)).obj
    ((HomotopyCategory.quotient C (.up ℤ)).obj K))
  simp only [Functor.comp_map] at hn ha hu
  erw [← hn]
  simp only [← Functor.map_comp_assoc]
  erw [hη, Functor.map_comp]
  simp only [Category.assoc]
  erw [← a.hom.naturality_assoc]
  erw [← A.rightDerivedFunctorUnit.naturality_assoc]
  erw [← reassoc_of% hc, hr, he]
  simp only [Functor.map_comp, Category.assoc]
  rfl

private theorem exact_factors_inv
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (U : C ⥤ D) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (K : CochainComplex C ℤ) :
    U.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) =
      (DerivedCategory.quotientCompQhIso D).hom.app
          ((U.mapHomologicalComplex (.up ℤ)).obj K) ≫
        U.mapDerivedCategoryFactors.inv.app K ≫
          U.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).inv.app K) := by
  apply (cancel_mono
    (U.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient C (.up ℤ)).obj K))).1
  rw [Iso.inv_hom_id_app, Functor.mapDerivedCategoryFactorsh_hom_app]
  have hf : (U.mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := rfl
  simp only [hf, Category.assoc, CategoryTheory.Functor.map_id,
    ← U.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    Category.id_comp, Iso.inv_hom_id_app_assoc]
  erw [Iso.hom_inv_id_app_assoc]
  exact (DerivedCategory.Qh.map_id _).symm

private theorem complex_unit_pasting
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    [Abelian.HasKInjectiveResolutions F]
    (P : C ⥤ D) (H : D ⥤ C) (A : C ⥤ E) (B : D ⥤ F) (U : F ⥤ E)
    [P.Additive] [H.Additive] [A.Additive] [B.Additive] [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {LP : DerivedCategory C ⥤ DerivedCategory D}
    {DA : DerivedCategory C ⥤ DerivedCategory E}
    {DB : DerivedCategory D ⥤ DerivedCategory F}
    (a : A.rightDerivedFunctor ≅ DA) (b : B.rightDerivedFunctor ≅ DB)
    (v : H ⋙ A ≅ B ⋙ U) (r : H.rightDerivedFunctor ⋙ DA ≅ DB ⋙ U.mapDerivedCategory)
    (hr : ∀ J : HomotopyCategory D (.up ℤ),
      (Functor.rightDerivedFunctorCompUnit H A).app J ≫
        a.hom.app (H.rightDerivedFunctor.obj (DerivedCategory.Qh.obj J)) ≫
        r.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((v.hom.mapHomotopyCategory (.up ℤ)).app J) ≫
        (B ⋙ U).rightDerivedFunctorUnit.app J ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso B U ≪≫
          Functor.isoWhiskerRight b U.mapDerivedCategory).hom.app (DerivedCategory.Qh.obj J))
    (η : 𝟭 _ ⟶ LP ⋙ H.rightDerivedFunctor)
    (ε : DerivedCategory.Qh ⋙ LP ⟶ P.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (K : CochainComplex C ℤ)
    (e : K ⟶ (H.mapHomologicalComplex (.up ℤ)).obj
      ((P.mapHomologicalComplex (.up ℤ)).obj K))
    (hη : η.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj K)) ≫
      H.rightDerivedFunctor.map (ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj K)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map e) ≫
        H.rightDerivedFunctorUnit.app ((P.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient C (.up ℤ)).obj K))) :
    let PK := (P.mapHomologicalComplex (.up ℤ)).obj K
    let Y := (B.mapHomologicalComplex (.up ℤ)).obj PK
    let cA := (DerivedCategory.quotientCompQhIso E).inv.app
        ((A.mapHomologicalComplex (.up ℤ)).obj K) ≫
      A.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
      A.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app K) ≫
      a.hom.app (DerivedCategory.Q.obj K)
    let cB := (DerivedCategory.quotientCompQhIso F).inv.app Y ≫
      B.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient D (.up ℤ)).obj PK) ≫
      B.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso D).hom.app PK) ≫
      b.hom.app (DerivedCategory.Q.obj PK)
    let d := LP.map ((DerivedCategory.quotientCompQhIso C).inv.app K) ≫
      ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
      (DerivedCategory.quotientCompQhIso D).hom.app PK
    cA ≫ DA.map (η.app (DerivedCategory.Q.obj K)) ≫
      r.hom.app (LP.obj (DerivedCategory.Q.obj K)) ≫
      U.mapDerivedCategory.map (DB.map d) =
    DerivedCategory.Q.map
        ((A.mapHomologicalComplex (.up ℤ)).map e ≫
          (v.hom.mapHomologicalComplex (.up ℤ)).app PK) ≫
      U.mapDerivedCategoryFactors.inv.app Y ≫ U.mapDerivedCategory.map cB := by
  intro PK Y cA cB d
  have h₀ := homotopy_unit_pasting P H A B U a b v r hr η ε K e hη
  have hn := r.hom.naturality (LP.map ((DerivedCategory.quotientCompQhIso C).inv.app K))
  have hu := η.naturality ((DerivedCategory.quotientCompQhIso C).inv.app K)
  simp only [Functor.comp_map, Functor.id_map] at hn hu
  dsimp only [cA, cB, d]
  simp only [Functor.map_comp, Category.assoc]
  erw [a.hom.naturality_assoc]
  erw [← reassoc_of% hn]
  have hcancel : (DerivedCategory.quotientCompQhIso C).hom.app K ≫
      η.app (DerivedCategory.Q.obj K) ≫
      H.rightDerivedFunctor.map (LP.map ((DerivedCategory.quotientCompQhIso C).inv.app K)) =
      η.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj K)) := by
    rw [← hu, Iso.hom_inv_id_app_assoc]
    rfl
  simp only [← DA.map_comp_assoc]
  rw [hcancel]
  have hh := congrArg (fun z ↦ (DerivedCategory.quotientCompQhIso E).inv.app
      ((A.mapHomologicalComplex (.up ℤ)).obj K) ≫ z ≫
      U.mapDerivedCategory.map (DB.map ((DerivedCategory.quotientCompQhIso D).hom.app PK))) h₀
  simp only [Category.assoc] at hh
  erw [hh]
  simp only [← U.mapDerivedCategory.map_comp]
  erw [b.hom.naturality]
  erw [exact_factors_inv U Y]
  simp only [Category.assoc]
  erw [← DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  erw [Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rfl

private theorem homEquiv_identity_factorization
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {P : C ⥤ D} {H : D ⥤ C} (adj : P ⊣ H) (Q₁ : C ⥤ C') (Q₂ : D ⥤ D')
    {LP : C' ⥤ D'} {RH : D' ⥤ C'} (a : LP ⊣ RH) (M : C)
    (ε : LP.obj (Q₁.obj M) ⟶ Q₂.obj (P.obj M))
    (β : Q₁.obj (H.obj (P.obj M)) ⟶ RH.obj (Q₂.obj (P.obj M)))
    (h : a.homEquiv (Q₁.obj M) (Q₂.obj (P.obj M)) (ε ≫ Q₂.map (𝟙 _)) =
      Q₁.map (adj.homEquiv M (P.obj M) (𝟙 _)) ≫ β) :
    a.unit.app (Q₁.obj M) ≫ RH.map ε = Q₁.map (adj.unit.app M) ≫ β := by
  rw [Adjunction.homEquiv_id] at h
  simpa only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id,
    CategoryTheory.Category.comp_id] using h

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

-- Match the affine sheaf module carriers in the pinned adjunction.
-- Match the chosen left-derived counit across the scheme module abbreviation.
private theorem pinned_unit_fac
    {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R)
    [(Scheme.Modules.tensorPullback g).Additive]
    (J : HomotopyCategory
      (SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace)) (.up ℤ)) :
    (canonicalPullbackAdjunction g).unit.app (DerivedCategory.Qh.obj J) ≫
        (schemeDerivedDirectImage g).map
          (((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition))
            g).app J) =
      (DerivedCategory.Qh
        (C := SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))).map
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
          g)).mapHomotopyCategory (.up ℤ)).unit.app J) ≫
        (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj J) := by
  have h := Classical.choose_spec (exists_schemeDerivedAdjunction g
    (hAdd := (Classical.choose exists_derivedPullbackComposition) g)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) g)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) g))
  have hh := h J (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj J)
    (𝟙 _)
  exact homEquiv_identity_factorization
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).mapHomotopyCategory
      (.up ℤ))
    (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace)))
    (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace)))
    (canonicalPullbackAdjunction g) J _ _ hh

variable [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- Before cancelling comparisons, the normalized derived pullback unit agrees with
its ordinary model. This identity holds for every complex, without K-flatness.
Source: Stacks Project, perfect.tex, Tag 0AA7, normalized derived unit calculation;
Mathlib CategoryTheory.Adjunction.derivedη_fac_app.
(blueprint: new-affine-pullback-sections-unit-uncancelled).
Proof: evaluate the normalized Hom equivalence in exists_schemeDerivedAdjunction
at the identity of termwise pullback of K. This factors the derived unit followed
by derived direct image of the fixed left-derived counit as the localized ordinary
unit followed by the direct-image right-derived unit. Apply derived R-sections and
precompose with its comparison. Naturality moves this comparison past the ordinary
unit. The factorization of rightDerivedFunctorCompUnit replaces the two successive
right-derived units by the composition unit. Naturality of r moves the counit past
r. Apply hr at the homotopy object of the termwise pullback. Naturality of the exact
restriction localization factors and of the sections comparison gives the right
side below. Finally Q/Qh transport naturality changes all homotopy maps into the
shown complex maps. This proves an equality of fixed morphisms and assumes no
comparison invertible; hence it also applies to zero complexes and arbitrary v
satisfying hr. It does not assert compatibility for an arbitrary isomorphism b. -/
theorem affinePullbackSections_unit_uncancelled
    {R B : CommRingCat.{u}} (g : Spec B ⟶ Spec R)
    (v : RingedSpace.moduleDirectImage g.toLRSHom.toShHom ⋙
        affineGlobalSections (𝟙 (Spec R)) ≅
      affineGlobalSections (𝟙 (Spec B)) ⋙
        ModuleCat.restrictScalars.{u} (affineBaseRingMap g))
    (r : schemeDerivedDirectImage g ⋙ affineDerivedGlobalSections (𝟙 (Spec R)) ≅
      affineDerivedGlobalSections (𝟙 (Spec B)) ⋙
        (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory)
    (hr : ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace)) (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (RingedSpace.moduleDirectImage g.toLRSHom.toShHom)
          (affineGlobalSections (𝟙 (Spec R)))).app J ≫
        (affineGlobalSectionsDerivedIso (𝟙 (Spec R))).hom.app
          ((schemeDerivedDirectImage g).obj (DerivedCategory.Qh.obj J)) ≫
        r.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((v.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (affineGlobalSections (𝟙 (Spec B)) ⋙
          ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).rightDerivedFunctorUnit.app J ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
            (affineGlobalSections (𝟙 (Spec B)))
            (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)) ≪≫
          Functor.isoWhiskerRight (affineGlobalSectionsDerivedIso (𝟙 (Spec B)))
            (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory).hom.app
          (DerivedCategory.Qh.obj J))
    [(Scheme.Modules.tensorPullback g).Additive]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace)) ℤ) :
    let P := Scheme.Modules.tensorPullback g
    let U := ModuleCat.restrictScalars.{u} (affineBaseRingMap g)
    let adjP := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
    let PK := (P.mapHomologicalComplex (.up ℤ)).obj K
    let Y := ((affineGlobalSections (𝟙 (Spec B))).mapHomologicalComplex (.up ℤ)).obj PK
    affineModelSectionsComparison R K ≫
        (affineDerivedGlobalSections (𝟙 (Spec R))).map
          ((canonicalPullbackAdjunction g).unit.app (DerivedCategory.Q.obj K)) ≫
        r.hom.app ((derivedPullback g).obj (DerivedCategory.Q.obj K)) ≫
        U.mapDerivedCategory.map
          ((affineDerivedGlobalSections (𝟙 (Spec B))).map
            (affineModelPullbackComparison g K)) =
      DerivedCategory.Q.map
        (((affineGlobalSections (𝟙 (Spec R))).mapHomologicalComplex (.up ℤ)).map
            ((adjP.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
          (v.hom.mapHomologicalComplex (.up ℤ)).app PK) ≫
        U.mapDerivedCategoryFactors.inv.app Y ≫
        U.mapDerivedCategory.map (affineModelSectionsComparison B PK) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf]
  have hp := pinned_unit_fac g ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
  have ht := Adjunction.mapHomotopyCategory_unit_app_quotient (.up ℤ)
    (C := SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
    (D := SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace))
    (R := RingedSpace.moduleDirectImage g.toLRSHom.toShHom)
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)) K
  have hp' := hp.trans (congrArg (fun f ↦
    (DerivedCategory.Qh
      (C := SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))).map f ≫
      (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit.app
        (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) ht)
  exact complex_unit_pasting
    (C := SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace))
    (D := SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace))
    (E := ModuleCat.{u} R) (F := ModuleCat.{u} B) (Scheme.Modules.tensorPullback g)
    (RingedSpace.moduleDirectImage g.toLRSHom.toShHom)
    (affineGlobalSections (𝟙 (Spec R))) (affineGlobalSections (𝟙 (Spec B)))
    (ModuleCat.restrictScalars.{u} (affineBaseRingMap g))
    (affineGlobalSectionsDerivedIso (𝟙 (Spec R)))
    (affineGlobalSectionsDerivedIso (𝟙 (Spec B))) v r hr
    (canonicalPullbackAdjunction g).unit
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) g)
    K (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
      g)).mapHomologicalComplex (.up ℤ)).unit.app K) hp'

end AlgebraicGeometry
