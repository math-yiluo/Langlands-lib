/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.SixFunctors.MixedDerivedMateUnit
import WeilConjectures.AlgebraicGeometry.ProperGraphTransfer.EtaleProperGraphTransfer
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection

/-! # Unit calculus for exact-derived transposition -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local instance 2000] Abelian.toPreadditive
attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  derivedEtaleLowerShriekUpperStarAdjunction
  derivedOpenImmersionLowerShriekUpperStarAdjunction
  openImmersionLowerShriekUpperStarAdjunction etaleLowerShriekUpperStarAdjunction
  upperStarLowerStarAdjunction Adjunction.mapDerivedCategoryAdjunction

private noncomputable def localizedExactAdj
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R) :
    L.mapDerivedCategory ⊣ R.mapDerivedCategory :=
  letI : CatCommSq (L.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q L.mapDerivedCategory :=
    ⟨L.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (R.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q R.mapDerivedCategory :=
    ⟨R.mapDerivedCategoryFactors.symm⟩
  (a.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso D (.up ℤ))
    L.mapDerivedCategory R.mapDerivedCategory

private lemma localizedExactAdj_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R)
    (X : HomotopyCategory C (.up ℤ)) :
    (localizedExactAdj a).unit.app (DerivedCategory.Qh.obj X) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app X) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app X) := by
  obtain ⟨J, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  change (localizedExactAdj a).unit.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj J)) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient C (.up ℤ)).obj J)) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((L.mapHomologicalComplex (.up ℤ)).obj J)) = _
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app,
    Functor.mapHomotopyCategoryFactors, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
  repeat first
    | erw [CategoryTheory.Functor.map_id]
    | erw [Category.id_comp]
    | erw [Category.comp_id]
  change (localizedExactAdj a).unit.app (DerivedCategory.Q.obj J) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app J) ≫
      R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj J) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app J)
  unfold localizedExactAdj
  rw [Adjunction.localization_unit_app]
  change (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app J) ≫
      R.mapDerivedCategoryFactors.inv.app _ ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app J)) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app J) ≫
      R.mapDerivedCategoryFactors.hom.app _ = _
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app,
    Category.comp_id]

private theorem etale_unit_fac (A : Type (u + 1)) [CommRing A]
    {V Y : Scheme.{u}} (v : V ⟶ Y) [Etale v]
    (J : HomotopyCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance).unit.app
        (DerivedCategory.Qh.obj J) ≫
      (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.map
        ((etaleLowerShriek (ModuleCat.{u + 1} A) v
          inferInstance).mapDerivedCategoryFactorsh.hom.app J) ≫
      (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategoryFactorsh.hom.app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) v
          inferInstance).mapHomotopyCategory (.up ℤ) |>.obj J) =
    DerivedCategory.Qh.map
      (((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v
        inferInstance).mapHomotopyCategory (.up ℤ)).unit.app J) := by
  unfold derivedEtaleLowerShriekUpperStarAdjunction
  exact localizedExactAdj_unit
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance) J

private lemma homEquiv_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (L : C ⥤ D) (R : D ⥤ C) (LD : C' ⥤ D') (RD : D' ⥤ C')
    (QC : C ⥤ C') (QD : D ⥤ D') (a : L ⊣ R) (ad : LD ⊣ RD)
    (eL : QC ⋙ LD ≅ L ⋙ QD) (eR : QD ⋙ RD ≅ R ⋙ QC)
    (hu : ∀ X, ad.unit.app (QC.obj X) ≫ RD.map (eL.hom.app X) ≫
      eR.hom.app (L.obj X) = QC.map (a.unit.app X))
    (X : C) (M : D) {K : D'} (t : L.obj X ⟶ M) (κ : QD.obj M ⟶ K) :
    ad.homEquiv _ _ (eL.hom.app X ≫ QD.map t ≫ κ) =
      QC.map (a.homEquiv _ _ t) ≫ eR.inv.app M ≫ RD.map κ := by
  have hη : ad.unit.app (QC.obj X) ≫ RD.map (eL.hom.app X) =
      QC.map (a.unit.app X) ≫ eR.inv.app (L.obj X) := by
    rw [← hu X, Category.assoc, Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hη]
  rw [← reassoc_of% eR.inv.naturality t]

private lemma exact_homEquiv_Qh
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : L ⊣ R) (ad : L.mapDerivedCategory ⊣ R.mapDerivedCategory)
    (hu : ∀ X, ad.unit.app (DerivedCategory.Qh.obj X) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app X) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app X))
    (X : HomotopyCategory C (.up ℤ)) (M : HomotopyCategory D (.up ℤ))
    {K : DerivedCategory D}
    (t : (L.mapHomotopyCategory (.up ℤ)).obj X ⟶ M)
    (κ : DerivedCategory.Qh.obj M ⟶ K) :
    ad.homEquiv _ _ (L.mapDerivedCategoryFactorsh.hom.app X ≫
      DerivedCategory.Qh.map t ≫ κ) =
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).homEquiv _ _ t) ≫
      R.mapDerivedCategoryFactorsh.inv.app M ≫ R.mapDerivedCategory.map κ := by
  exact homEquiv_transport (L.mapHomotopyCategory (.up ℤ))
    (R.mapHomotopyCategory (.up ℤ)) L.mapDerivedCategory R.mapDerivedCategory
    DerivedCategory.Qh DerivedCategory.Qh (a.mapHomotopyCategory (.up ℤ)) ad
    L.mapDerivedCategoryFactorsh R.mapDerivedCategoryFactorsh hu X M t κ

private lemma comp_homotopy_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (K : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K = 𝟙 _ := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  change (HomotopyCategory.quotient E (.up ℤ)).map (𝟙 _) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

private lemma mixed_mate_unit_normal
    {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
    [Abelian C] [Abelian D] [Abelian E] [Abelian V]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory V]
    [Abelian.HasKInjectiveResolutions E] [Abelian.HasKInjectiveResolutions V]
    (T : C ⥤ D) (L' : D ⥤ V) (L : C ⥤ E) (O : E ⥤ V)
    (R : E ⥤ C) (P : V ⥤ D)
    [T.Additive] [L'.Additive] [L.Additive] [O.Additive] [R.Additive] [P.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    (adj : L ⊣ R) (adj' : L' ⊣ P) (e : T ⋙ L' ≅ L ⋙ O)
    (β : T.mapDerivedCategory ⋙ L'.mapDerivedCategory ⟶
      L.mapDerivedCategory ⋙ O.mapDerivedCategory)
    (hβ : (Functor.mapDerivedCategorySquareIso e).hom = β)
    (K : HomotopyCategory E (.up ℤ)) :
    T.mapDerivedCategoryFactorsh.inv.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
      T.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
      (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
        adj'.mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _ β)).app (DerivedCategory.Qh.obj K) =
    DerivedCategory.Qh.map
      (((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.hom)).mapHomotopyCategory
        (.up ℤ)).app K) ≫
      P.rightDerivedFunctorUnit.app ((O.mapHomotopyCategory (.up ℤ)).obj K) ≫
      P.rightDerivedFunctor.map (O.mapDerivedCategoryFactorsh.inv.app K) := by
  have hm := mixedDerivedMateUnit T L' L O R P adj adj' e β hβ K
  simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    comp_homotopy_inv, Category.comp_id] at hm
  erw [Category.id_comp] at hm
  apply (cancel_mono (P.rightDerivedFunctor.map (O.mapDerivedCategoryFactorsh.hom.app K))).1
  simp only [Category.assoc]
  erw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.comp_id]
  erw [hm, Iso.inv_hom_id_app_assoc]

private lemma baseChange_unit_normal
    (A : Type (u + 1)) [CommRing A]
    {Z V Y : Scheme.{u}} (g : Z ⟶ Y) (v : V ⟶ Y)
    (J : HomotopyCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategoryFactorsh.inv.app
        ((lowerStar (ModuleCat.{u + 1} A) g).mapHomotopyCategory (.up ℤ) |>.obj J) ≫
      (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.map
        ((lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorUnit.app J) ≫
      (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback g v).toCommSq).app (DerivedCategory.Qh.obj J) =
    DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory
        (baseChangeMap (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback g v).toCommSq) (.up ℤ)).app J) ≫
      (lowerStar (ModuleCat.{u + 1} A) (pullback.snd g v)).rightDerivedFunctorUnit.app
        ((upperStar (ModuleCat.{u + 1} A) (pullback.fst g v)).mapHomotopyCategory
          (.up ℤ) |>.obj J) ≫
      (lowerStar (ModuleCat.{u + 1} A) (pullback.snd g v)).rightDerivedFunctor.map
        ((upperStar (ModuleCat.{u + 1} A)
          (pullback.fst g v)).mapDerivedCategoryFactorsh.inv.app J) := by
  exact mixed_mate_unit_normal (upperStar (ModuleCat.{u + 1} A) v)
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd g v))
    (upperStar (ModuleCat.{u + 1} A) g)
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst g v))
    (lowerStar (ModuleCat.{u + 1} A) g)
    (lowerStar (ModuleCat.{u + 1} A) (pullback.snd g v))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (pullback.snd g v))
    (squareUpperStarIso (ModuleCat.{u + 1} A) (IsPullback.of_hasPullback g v).toCommSq)
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback g v).toCommSq).hom rfl J

private lemma transpose_baseChange_normal
    {D E Z S : Type*} [Category D] [Category E] [Category Z] [Category S]
    [Abelian D] [Abelian E] [Abelian Z] [Abelian S]
    [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory Z] [HasDerivedCategory S]
    [Abelian.HasKInjectiveResolutions Z] [Abelian.HasKInjectiveResolutions S]
    (L : D ⥤ E) (R : E ⥤ D) (G : Z ⥤ E) (T : Z ⥤ S) (P : S ⥤ D)
    [L.Additive] [R.Additive] [G.Additive] [T.Additive] [P.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (a : L ⊣ R) (ad : L.mapDerivedCategory ⊣ R.mapDerivedCategory)
    (hu : ∀ X, ad.unit.app (DerivedCategory.Qh.obj X) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app X) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app X))
    (βD : G.rightDerivedFunctor ⋙ R.mapDerivedCategory ⟶
      T.mapDerivedCategory ⋙ P.rightDerivedFunctor)
    (M : HomotopyCategory Z (.up ℤ))
    (βh : (R.mapHomotopyCategory (.up ℤ)).obj ((G.mapHomotopyCategory (.up ℤ)).obj M) ⟶
      (P.mapHomotopyCategory (.up ℤ)).obj ((T.mapHomotopyCategory (.up ℤ)).obj M))
    (hb : R.mapDerivedCategoryFactorsh.inv.app ((G.mapHomotopyCategory (.up ℤ)).obj M) ≫
      R.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app M) ≫
        βD.app (DerivedCategory.Qh.obj M) =
      DerivedCategory.Qh.map βh ≫
        P.rightDerivedFunctorUnit.app ((T.mapHomotopyCategory (.up ℤ)).obj M) ≫
        P.rightDerivedFunctor.map (T.mapDerivedCategoryFactorsh.inv.app M))
    (X : HomotopyCategory D (.up ℤ)) {K : DerivedCategory Z}
    (t : (L.mapHomotopyCategory (.up ℤ)).obj X ⟶
      (G.mapHomotopyCategory (.up ℤ)).obj M)
    (k : DerivedCategory.Qh.obj M ⟶ K) :
    ad.homEquiv _ _ (L.mapDerivedCategoryFactorsh.hom.app X ≫
        DerivedCategory.Qh.map t ≫ G.rightDerivedFunctorUnit.app M ≫
        G.rightDerivedFunctor.map k) ≫ βD.app K =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).homEquiv _ _ t ≫ βh) ≫
        P.rightDerivedFunctorUnit.app ((T.mapHomotopyCategory (.up ℤ)).obj M) ≫
        P.rightDerivedFunctor.map
          (T.mapDerivedCategoryFactorsh.inv.app M ≫ T.mapDerivedCategory.map k) := by
  have hn := βD.naturality k
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [exact_homEquiv_Qh L R a ad hu]
  simp only [Functor.map_comp, Category.assoc]
  rw [hn, reassoc_of% hb]

/-- Exact-derived transposition and mixed base change commute with the homotopy unit.
The proof transports the exact adjunction unit, then applies naturality and the
mixed base-change unit identity. Source: Stacks Project Tags 0D6E and 0F7B.
(blueprint: lem-pur-proper-sheaf-transpose-unit-calculus). -/
theorem exactDerivedTranspose_baseChange_normal
    {C D E Z S : Type*} [Category C] [Category D] [Category E]
    [Category Z] [Category S]
    [Abelian C] [Abelian D] [Abelian E] [Abelian Z] [Abelian S]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory Z] [HasDerivedCategory S]
    [Abelian.HasKInjectiveResolutions Z] [Abelian.HasKInjectiveResolutions S]
    (Q : C ⥤ D) (L : D ⥤ E) (R : E ⥤ D)
    (O : C ⥤ Z) (G : Z ⥤ E) (T : Z ⥤ S) (P : S ⥤ D)
    [Q.Additive] [L.Additive] [R.Additive] [O.Additive] [G.Additive]
    [T.Additive] [P.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (a : L ⊣ R) (ad : L.mapDerivedCategory ⊣ R.mapDerivedCategory)
    (hu : ∀ X, ad.unit.app (DerivedCategory.Qh.obj X) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app X) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app X))
    (βD : G.rightDerivedFunctor ⋙ R.mapDerivedCategory ⟶
      T.mapDerivedCategory ⋙ P.rightDerivedFunctor)
    (β : G ⋙ R ⟶ T ⋙ P)
    (hb : ∀ M, R.mapDerivedCategoryFactorsh.inv.app ((G.mapHomotopyCategory (.up ℤ)).obj M) ≫
      R.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app M) ≫
        βD.app (DerivedCategory.Qh.obj M) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory β (.up ℤ)).app M) ≫
        P.rightDerivedFunctorUnit.app ((T.mapHomotopyCategory (.up ℤ)).obj M) ≫
        P.rightDerivedFunctor.map (T.mapDerivedCategoryFactorsh.inv.app M))
    (τ : Q ⋙ L ⟶ O ⋙ G) (J : HomotopyCategory C (.up ℤ)) :
    ad.homEquiv _ _ (L.mapDerivedCategoryFactorsh.hom.app
          ((Q.mapHomotopyCategory (.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory τ (.up ℤ)).app J) ≫
        (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit O G).app J) ≫
        βD.app (O.mapDerivedCategory.obj (DerivedCategory.Qh.obj J)) =
      DerivedCategory.Qh.map
        ((a.mapHomotopyCategory (.up ℤ)).homEquiv
            ((Q.mapHomotopyCategory (.up ℤ)).obj J)
            ((G.mapHomotopyCategory (.up ℤ)).obj ((O.mapHomotopyCategory (.up ℤ)).obj J))
            ((NatTrans.mapHomotopyCategory τ (.up ℤ)).app J) ≫
          (NatTrans.mapHomotopyCategory β (.up ℤ)).app
            ((O.mapHomotopyCategory (.up ℤ)).obj J)) ≫
        P.rightDerivedFunctorUnit.app
          ((T.mapHomotopyCategory (.up ℤ)).obj ((O.mapHomotopyCategory (.up ℤ)).obj J)) ≫
        P.rightDerivedFunctor.map
          (T.mapDerivedCategoryFactorsh.inv.app ((O.mapHomotopyCategory (.up ℤ)).obj J) ≫
            T.mapDerivedCategory.map (O.mapDerivedCategoryFactorsh.inv.app J)) := by
  have h := transpose_baseChange_normal L R G T P a ad hu βD
    ((O.mapHomotopyCategory (.up ℤ)).obj J)
    ((NatTrans.mapHomotopyCategory β (.up ℤ)).app ((O.mapHomotopyCategory (.up ℤ)).obj J))
    (hb ((O.mapHomotopyCategory (.up ℤ)).obj J))
    ((Q.mapHomotopyCategory (.up ℤ)).obj J)
    ((NatTrans.mapHomotopyCategory τ (.up ℤ)).app J)
    (O.mapDerivedCategoryFactorsh.inv.app J)
  rw [Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app]
  erw [comp_homotopy_inv, DerivedCategory.Qh.map_id, Category.id_comp]
  exact h

end AlgebraicGeometry.Etale
