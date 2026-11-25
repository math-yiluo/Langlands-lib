/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.ProperGraphTransfer.EtaleProperGraphTransfer
import WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange

/-! # Exact derived triangular mates -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Adjunction.mapDerivedCategoryAdjunction

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

private lemma homotopy_triangle_relation
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    (I : C ⥤ D) (U : D ⥤ C) (L : C ⥤ E) (R : E ⥤ C) (T : D ⥤ E)
    [I.Additive] [U.Additive] [L.Additive] [R.Additive] [T.Additive]
    (ai : I ⊣ U) (aa : L ⊣ R) (e : U ⟶ T ⋙ R) (σ : L ⟶ I ⋙ T)
    (h : ∀ F, aa.unit.app F ≫ R.map (σ.app F) = ai.unit.app F ≫ e.app (I.obj F))
    (J : HomotopyCategory C (.up ℤ)) :
    (aa.mapHomotopyCategory (.up ℤ)).homEquiv _ _
      ((NatTrans.mapHomotopyCategory σ (.up ℤ)).app J) =
      (ai.mapHomotopyCategory (.up ℤ)).unit.app J ≫
        (NatTrans.mapHomotopyCategory e (.up ℤ)).app
          ((I.mapHomotopyCategory (.up ℤ)).obj J) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective J
  simp only [Adjunction.homEquiv_unit]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_unit_app_quotient]
  change (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _ =
    (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n : 1
  exact h (K.X n)

private lemma triangle_mate_normal_core
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (I : C ⥤ D) (U : D ⥤ C) (L : C ⥤ E) (R : E ⥤ C) (T : D ⥤ E)
    [I.Additive] [U.Additive] [L.Additive] [R.Additive] [T.Additive]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (ai : I ⊣ U) (aa : L ⊣ R)
    (adi : I.mapDerivedCategory ⊣ U.mapDerivedCategory)
    (ada : L.mapDerivedCategory ⊣ R.mapDerivedCategory)
    (hui : ∀ X, adi.unit.app (DerivedCategory.Qh.obj X) ≫
      U.mapDerivedCategory.map (I.mapDerivedCategoryFactorsh.hom.app X) ≫
      U.mapDerivedCategoryFactorsh.hom.app ((I.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((ai.mapHomotopyCategory (.up ℤ)).unit.app X))
    (hua : ∀ X, ada.unit.app (DerivedCategory.Qh.obj X) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app X) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((aa.mapHomotopyCategory (.up ℤ)).unit.app X))
    (e : U ≅ T ⋙ R) (J : HomotopyCategory C (.up ℤ))
    (σ : (L.mapHomotopyCategory (.up ℤ)).obj J ⟶
      (T.mapHomotopyCategory (.up ℤ)).obj ((I.mapHomotopyCategory (.up ℤ)).obj J))
    (hσ : (aa.mapHomotopyCategory (.up ℤ)).homEquiv _ _ σ =
      (ai.mapHomotopyCategory (.up ℤ)).unit.app J ≫
        (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
          ((I.mapHomotopyCategory (.up ℤ)).obj J)) :
    (ada.homEquiv _ _).symm (adi.unit.app (DerivedCategory.Qh.obj J) ≫
      (Functor.mapDerivedCategoryTriangleIso e).hom.app
        (I.mapDerivedCategory.obj (DerivedCategory.Qh.obj J))) =
      L.mapDerivedCategoryFactorsh.hom.app J ≫ DerivedCategory.Qh.map σ ≫
        T.mapDerivedCategoryFactorsh.inv.app ((I.mapHomotopyCategory (.up ℤ)).obj J) ≫
        T.mapDerivedCategory.map (I.mapDerivedCategoryFactorsh.inv.app J) := by
  let X := (I.mapHomotopyCategory (.up ℤ)).obj J
  let M := (T.mapHomotopyCategory (.up ℤ)).obj X
  let κ := T.mapDerivedCategoryFactorsh.inv.app X ≫
    T.mapDerivedCategory.map (I.mapDerivedCategoryFactorsh.inv.app J)
  have ht := Functor.mapDerivedCategoryTriangleIso_hom_app_Qh_obj e X
  rw [comp_homotopy_inv, Category.comp_id] at ht
  have ht' : (Functor.mapDerivedCategoryTriangleIso e).hom.app (DerivedCategory.Qh.obj X) ≫
      R.mapDerivedCategory.map (T.mapDerivedCategoryFactorsh.hom.app X) ≫
      R.mapDerivedCategoryFactorsh.hom.app M =
      U.mapDerivedCategoryFactorsh.hom.app X ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app X) := by
    apply (cancel_epi (U.mapDerivedCategoryFactorsh.inv.app X)).1
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using ht
  apply (ada.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  change _ = ada.homEquiv _ _ (L.mapDerivedCategoryFactorsh.hom.app J ≫
    DerivedCategory.Qh.map σ ≫ κ)
  rw [exact_homEquiv_Qh L R aa ada hua]
  let z := R.mapDerivedCategory.mapIso
    (T.mapDerivedCategory.mapIso (I.mapDerivedCategoryFactorsh.app J) ≪≫
      T.mapDerivedCategoryFactorsh.app X) ≪≫ R.mapDerivedCategoryFactorsh.app M
  have hc : R.mapDerivedCategoryFactorsh.inv.app M ≫
      R.mapDerivedCategory.map κ ≫
      R.mapDerivedCategory.map (T.mapDerivedCategory.map
        (I.mapDerivedCategoryFactorsh.hom.app J)) ≫
      R.mapDerivedCategory.map (T.mapDerivedCategoryFactorsh.hom.app X) ≫
      R.mapDerivedCategoryFactorsh.hom.app M = 𝟙 _ := by
    simpa only [z, κ, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Functor.map_comp,
      Category.assoc] using z.inv_hom_id
  apply (cancel_mono
    (R.mapDerivedCategory.map (T.mapDerivedCategory.map
      (I.mapDerivedCategoryFactorsh.hom.app J)) ≫
      R.mapDerivedCategory.map (T.mapDerivedCategoryFactorsh.hom.app X) ≫
      R.mapDerivedCategoryFactorsh.hom.app M)).1
  simp only [Category.assoc]
  rw [hc]
  erw [Category.comp_id]
  have hn := (Functor.mapDerivedCategoryTriangleIso e).hom.naturality
    (I.mapDerivedCategoryFactorsh.hom.app J)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn, ht', reassoc_of% hui J, hσ, DerivedCategory.Qh.map_comp]

private lemma triangle_derivedMate_generic
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (I : C ⥤ D) (U : D ⥤ C) (L : C ⥤ E) (R : E ⥤ C) (T : D ⥤ E)
    [I.Additive] [U.Additive] [L.Additive] [R.Additive] [T.Additive]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (ai : I ⊣ U) (aa : L ⊣ R)
    (adi : I.mapDerivedCategory ⊣ U.mapDerivedCategory)
    (ada : L.mapDerivedCategory ⊣ R.mapDerivedCategory)
    (hui : ∀ X, adi.unit.app (DerivedCategory.Qh.obj X) ≫
      U.mapDerivedCategory.map (I.mapDerivedCategoryFactorsh.hom.app X) ≫
      U.mapDerivedCategoryFactorsh.hom.app ((I.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((ai.mapHomotopyCategory (.up ℤ)).unit.app X))
    (hua : ∀ X, ada.unit.app (DerivedCategory.Qh.obj X) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app X) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((aa.mapHomotopyCategory (.up ℤ)).unit.app X))
    (e : U ≅ T ⋙ R) (σ : L ⟶ I ⋙ T)
    (hσ : ∀ F, aa.unit.app F ≫ R.map (σ.app F) = ai.unit.app F ≫ e.hom.app (I.obj F))
    (J : HomotopyCategory C (.up ℤ)) :
    (ada.homEquiv _ _).symm (adi.unit.app (DerivedCategory.Qh.obj J) ≫
      (Functor.mapDerivedCategoryTriangleIso e).hom.app
        (I.mapDerivedCategory.obj (DerivedCategory.Qh.obj J))) =
      L.mapDerivedCategoryFactorsh.hom.app J ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory σ (.up ℤ)).app J) ≫
        T.mapDerivedCategoryFactorsh.inv.app ((I.mapHomotopyCategory (.up ℤ)).obj J) ≫
        T.mapDerivedCategory.map (I.mapDerivedCategoryFactorsh.inv.app J) := by
  exact triangle_mate_normal_core I U L R T ai aa adi ada hui hua e J
    ((NatTrans.mapHomotopyCategory σ (.up ℤ)).app J)
    (homotopy_triangle_relation I U L R T ai aa e.hom σ hσ J)

/-- Exact localization carries the ordinary triangular adjunction unit relation
for an ordinary natural transformation to its derived adjunction mate.
Source: Stacks Project Tag 0F7B, functoriality of the graph adjunct through localization.
(blueprint: lem-pur-proper-graph-derived-mate). -/
theorem properGraphTriangle_derivedMate
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).obj X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C]
    [Abelian.HasKInjectiveResolutions D] [Abelian.HasKInjectiveResolutions E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (I : C ⥤ D) (U : D ⥤ C) (L : C ⥤ E) (R : E ⥤ C) (T : D ⥤ E)
    [I.Additive] [U.Additive] [L.Additive] [R.Additive] [T.Additive]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (ai : I ⊣ U) (aa : L ⊣ R)
    (e : U ≅ T ⋙ R) (σ : L ⟶ I ⋙ T)
    (hσ : ∀ F, aa.unit.app F ≫ R.map (σ.app F) = ai.unit.app F ≫ e.hom.app (I.obj F))
    (J : HomotopyCategory C (.up ℤ)) :
    (aa.mapDerivedCategoryAdjunction.homEquiv _ _).symm
      (ai.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Qh.obj J) ≫
      (Functor.mapDerivedCategoryTriangleIso e).hom.app
        (I.mapDerivedCategory.obj (DerivedCategory.Qh.obj J))) =
      L.mapDerivedCategoryFactorsh.hom.app J ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory σ (.up ℤ)).app J) ≫
        T.mapDerivedCategoryFactorsh.inv.app ((I.mapHomotopyCategory (.up ℤ)).obj J) ≫
        T.mapDerivedCategory.map (I.mapDerivedCategoryFactorsh.inv.app J) := by
  exact triangle_derivedMate_generic I U L R T ai aa
    ai.mapDerivedCategoryAdjunction aa.mapDerivedCategoryAdjunction
    ai.mapDerivedCategoryAdjunction_unit_app_fac aa.mapDerivedCategoryAdjunction_unit_app_fac
    e σ hσ J

private lemma homotopy_normalized_transpose
    {C D E Z S : Type*} [Category C] [Category D] [Category E]
    [Category Z] [Category S]
    [Abelian C] [Abelian D] [Abelian E] [Abelian Z] [Abelian S]
    (Q : C ⥤ D) (L : D ⥤ E) (R : E ⥤ D)
    (I : C ⥤ Z) (G : Z ⥤ E) (T : Z ⥤ S) (P : S ⥤ D)
    [Q.Additive] [L.Additive] [R.Additive] [I.Additive] [G.Additive]
    [T.Additive] [P.Additive]
    (a : L ⊣ R) (τ : Q ⋙ L ⟶ I ⋙ G) (β : G ⋙ R ⟶ T ⋙ P)
    (U V : C ⥤ S) [U.Additive] [V.Additive]
    (e : Q ⟶ U ⋙ P) (γ : U ⟶ V) (σ : V ⟶ I ⋙ T)
    (h : ∀ F, a.homEquiv _ _ (τ.app F) ≫ β.app (I.obj F) =
      e.app F ≫ P.map (γ.app F ≫ σ.app F))
    (J : HomotopyCategory C (.up ℤ)) :
    (a.mapHomotopyCategory (.up ℤ)).homEquiv
        ((Q.mapHomotopyCategory (.up ℤ)).obj J)
        ((G.mapHomotopyCategory (.up ℤ)).obj ((I.mapHomotopyCategory (.up ℤ)).obj J))
        ((NatTrans.mapHomotopyCategory τ (.up ℤ)).app J) ≫
      (NatTrans.mapHomotopyCategory β (.up ℤ)).app
        ((I.mapHomotopyCategory (.up ℤ)).obj J) =
      (NatTrans.mapHomotopyCategory e (.up ℤ)).app J ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (U ⋙ P)) (.up ℤ)).inv.app J ≫
        (P.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory γ (.up ℤ)).app J ≫
            (NatTrans.mapHomotopyCategory σ (.up ℤ)).app J ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (I ⋙ T)) (.up ℤ)).inv.app J) := by
  simp only [comp_homotopy_inv, Category.id_comp, Category.comp_id]
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective J
  simp only [Adjunction.homEquiv_unit]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  simp only [Category.assoc]
  change (HomotopyCategory.quotient D (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient D (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient D (.up ℤ)).map _ =
    (HomotopyCategory.quotient D (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient D (.up ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n : 1
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Adjunction.mapHomologicalComplex_unit_app_f, NatTrans.mapHomologicalComplex_app_f]
  dsimp [Functor.mapHomologicalComplex, Functor.mapHomotopyCategory,
    HomotopyCategory.quotient, CategoryTheory.Quotient.lift, CategoryTheory.Quotient.functor]
  simpa only [Adjunction.homEquiv_unit, Category.assoc] using h (K.X n)

section
universe u
attribute [local instance 2000] Abelian.toPreadditive
attribute [local irreducible] lowerStar upperStar openImmersionLowerShriek
  openImmersionLowerShriekUpperStarAdjunction

private lemma graph_mate_canonical
    (A : Type (u + 1)) [CommRing A]
    {W V Y : Scheme.{u}} (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v]
    {f : W ⟶ Y} (hf : f = q ≫ v) (c : Compactification f)
    (J : HomotopyCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
        (ProperGraphTransfer.graph q v hf c)).mapDerivedCategoryAdjunction.homEquiv _ _).symm
      ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
          c.i).mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Qh.obj J) ≫
        (Functor.mapDerivedCategoryTriangleIso
          (upperStarComp (ModuleCat.{u + 1} A) (ProperGraphTransfer.graph q v hf c)
            (pullback.fst c.g v) c.i (ProperGraphTransfer.graph_fst q v hf c).symm)).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj
            (DerivedCategory.Qh.obj J))) =
    (openImmersionLowerShriek (ModuleCat.{u + 1} A)
        (ProperGraphTransfer.graph q v hf c)).mapDerivedCategoryFactorsh.hom.app J ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
        (openImmersionLowerShriekBaseChange (ModuleCat.{u + 1} A)
          (ProperGraphTransfer.graph q v hf c) (pullback.fst c.g v) c.i
          (ProperGraphTransfer.graph_fst q v hf c)) (.up ℤ)).app J) ≫
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g v)).mapDerivedCategoryFactorsh.inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapHomotopyCategory
          (.up ℤ) |>.obj J) ≫
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g v)).mapDerivedCategory.map
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
              c.i).mapDerivedCategoryFactorsh.inv.app J) := by
  let B := ModuleCat.{u + 1} A
  let a := ProperGraphTransfer.graph q v hf c
  let b := pullback.fst c.g v
  let L := openImmersionLowerShriek B a
  let R := upperStar B a
  let I := openImmersionLowerShriek B c.i
  let T := upperStar B b
  let ai := openImmersionLowerShriekUpperStarAdjunction B c.i
  let aa := openImmersionLowerShriekUpperStarAdjunction B a
  let e := upperStarComp B a b c.i (ProperGraphTransfer.graph_fst q v hf c).symm
  let σ := openImmersionLowerShriekBaseChange B a b c.i
    (ProperGraphTransfer.graph_fst q v hf c)
  have h := properGraphTriangle_derivedMate I (upperStar B c.i) L R T ai aa
    e σ (fun F => by
      simpa only [upperStarCompIso_eq] using
        unit_map_openImmersionLowerShriekBaseChange_app B a b c.i
          (ProperGraphTransfer.graph_fst q v hf c) F) J
  exact h

end

end AlgebraicGeometry.Etale
