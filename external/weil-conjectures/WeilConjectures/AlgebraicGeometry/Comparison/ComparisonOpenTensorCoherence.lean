/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison

/-!
# Comparison preserves the canonical open tensor map

Source: Stacks Project, Tags 0GL1, 0E8I and 07A4; the finite-coefficient transport
paragraph of the blueprint proof of `thm-sf-pf-proetale`
(blueprint: lem-sf-comparison-open-tensor-coherence).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace CategoryTheory

open _root_.CategoryTheory.Functor

private lemma unit_of_mate
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    (a : F ⊣ G) (b : F' ⊣ G') {U : C ⥤ C'} {V : D ⥤ D'}
    (β : U ⋙ F' ⟶ F ⋙ V) (τ : G ⋙ U ⟶ V ⋙ G')
    (h : (mateEquiv a b β) = τ) (K : C) :
    b.unit.app (U.obj K) ≫ G'.map (β.app K) =
      U.map (a.unit.app K) ≫ τ.app (F.obj K) := by
  rw [← h]
  exact (unit_mateEquiv a b β K).symm

private lemma conj_transport {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ R₁' R₂' : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : R₁ ≅ R₁') (f : R₂ ≅ R₂')
    (α : L₂ ⟶ L₁) :
    conjugateEquiv (a.ofNatIsoRight e) (b.ofNatIsoRight f) α =
      e.inv ≫ conjugateEquiv a b α ≫ f.hom := by
  ext X
  simp only [conjugateEquiv_apply_app, Adjunction.ofNatIsoRight_unit,
    Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [← f.hom.naturality_assoc, ← f.hom.naturality_assoc, ← f.hom.naturality]
  rw [← R₂.map_comp_assoc, ← α.naturality, R₂.map_comp_assoc]
  rw [← b.unit_naturality_assoc]

private lemma comp_transport {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : C ⥤ D} {R R' : D ⥤ C} {M : D ⥤ E} {S S' : E ⥤ D}
    (a : L ⊣ R) (b : M ⊣ S) (e : R ≅ R') (f : S ≅ S') :
    (a.ofNatIsoRight e).comp (b.ofNatIsoRight f) =
      (a.comp b).ofNatIsoRight
        (isoWhiskerLeft S e ≪≫ isoWhiskerRight f R') := by
  apply Adjunction.ext
  ext X
  simp only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Iso.trans_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, Functor.comp_obj,
    Functor.map_comp, Category.assoc]
  rw [← e.hom.naturality_assoc]

private lemma conjugate_inverse {C D : Type*} [Category* C] [Category* D]
    {F F' : C ⥤ D} {G G' : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G')
    (e : G ≅ G') :
    conjugateEquiv a b (((conjugateIsoEquiv a b).symm e).hom) = e.hom := by
  change (conjugateEquiv a b) ((conjugateEquiv a b).symm e.hom) = e.hom
  exact (conjugateEquiv a b).apply_symm_apply e.hom

private lemma transport_refl {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    adj.ofNatIsoRight (Iso.refl G) = adj := by
  apply Adjunction.ext
  ext M
  simp [Adjunction.ofNatIsoRight_unit]

def tensorTransport
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D)
    {F G : C ⥤ D} (e : F ≅ G)
    (m : (postcompose₂.obj F).obj T ≅ (((whiskeringLeft₂ D).obj F).obj F).obj U) :
    (postcompose₂.obj G).obj T ≅ (((whiskeringLeft₂ D).obj G).obj G).obj U :=
  (postcompose₂.mapIso e.symm).app T ≪≫ m ≪≫
    ((((whiskeringLeft₂ D).obj F).mapIso e).app U) ≪≫
    (((whiskeringLeft₂ D).mapIso e).app G).app U

private lemma conjugate_comp_transport
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {L : C ⥤ D} {R R' : D ⥤ C} {M : D ⥤ F} {S : F ⥤ D}
    {N : C ⥤ E} {T : E ⥤ C} {P : E ⥤ F} {Q Q' : F ⥤ E}
    (a : L ⊣ R) (b : M ⊣ S) (c : N ⊣ T) (d : P ⊣ Q)
    (e : R ≅ R') (f : Q ≅ Q') (α : N ⋙ P ⟶ L ⋙ M)
    (β : S ⋙ R ⟶ Q ⋙ T)
    (h : conjugateEquiv (a.comp b) (c.comp d) α = β) :
    conjugateEquiv ((a.ofNatIsoRight e).comp b) (c.comp (d.ofNatIsoRight f)) α =
      Functor.whiskerLeft S e.inv ≫ β ≫ Functor.whiskerRight f.hom T := by
  have h₁ := comp_transport a b e (Iso.refl _)
  have h₂ := comp_transport c d (Iso.refl _) f
  rw [transport_refl] at h₁ h₂
  rw [h₁, h₂, conj_transport, h]
  ext X
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.assoc]
  erw [Category.id_comp, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparisonCompatible_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : D ⥤ C} {F' : D' ⥤ C'}
    {N : D ⥤ D'} {M : C ⥤ C'} {N' : D ⥤ D'} {M' : C ⥤ C'}
    {T : D ⥤ D ⥤ D} {U : C ⥤ C ⥤ C}
    {T' : D' ⥤ D' ⥤ D'} {U' : C' ⥤ C' ⥤ C'}
    (a : N ⋙ F' ≅ F ⋙ M) (e : N ≅ N') (d : M ≅ M')
    (t : (postcompose₂.obj F).obj T ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj U)
    (t' : (postcompose₂.obj F').obj T' ⟶ (((whiskeringLeft₂ C').obj F').obj F').obj U')
    (m : (postcompose₂.obj M).obj U ≅ (((whiskeringLeft₂ C').obj M).obj M).obj U')
    (n : (postcompose₂.obj N).obj T ≅ (((whiskeringLeft₂ D').obj N).obj N).obj T')
    (h : Adjunction.ComparisonCompatible a t t' m n) :
    Adjunction.ComparisonCompatible
      (Functor.isoWhiskerRight e.symm F' ≪≫ a ≪≫ Functor.isoWhiskerLeft F d)
      t t' (tensorTransport U U' d m) (tensorTransport T T' e n) := by
  intro X Y
  have hh := h X Y
  simp only [tensorTransport, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.postcompose₂_map_app_app_app,
    Iso.app_hom, Functor.mapIso_hom, Functor.whiskeringLeft₂_map_app_app_app_app,
    Functor.whiskeringLeft₂_obj_map_app_app_app, Category.assoc]
  erw [d.inv.naturality_assoc, reassoc_of% hh]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [← F'.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have ht₁ := NatTrans.congr_app (t'.naturality (e.hom.app X)) (N'.obj Y)
  have ht₂ := (t'.app (N.obj X)).naturality (e.hom.app Y)
  dsimp at ht₁ ht₂
  rw [reassoc_of% ht₁, reassoc_of% ht₂]
  simp only [← NatTrans.comp_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [NatTrans.naturality_assoc]
  erw [(U'.map (d.hom.app (F.obj X))).naturality
    (a.hom.app Y ≫ d.hom.app (F.obj Y))]
  simp only [NatTrans.comp_app, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    NatTrans.comp_app, Category.assoc]
  simp only [Functor.map_comp]
  rfl

private lemma inverse_tensor_square
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {F : C ⥤ D} {F' : C' ⥤ D'} {N : C ⥤ C'} {M : D ⥤ D'}
    {T : C ⥤ C ⥤ C} {U : D ⥤ D ⥤ D}
    {T' : C' ⥤ C' ⥤ C'} {U' : D' ⥤ D' ⥤ D'}
    (a : N ⋙ F' ≅ F ⋙ M)
    (t : (postcompose₂.obj F).obj T ≅ (((whiskeringLeft₂ D).obj F).obj F).obj U)
    (t' : (postcompose₂.obj F').obj T' ≅ (((whiskeringLeft₂ D').obj F').obj F').obj U')
    (m : (postcompose₂.obj M).obj U ≅ (((whiskeringLeft₂ D').obj M).obj M).obj U')
    (n : (postcompose₂.obj N).obj T ≅ (((whiskeringLeft₂ C').obj N).obj N).obj T')
    (h : Adjunction.ComparisonCompatible a t.hom t'.hom m n) (X Y : C) :
    M.map ((t.inv.app X).app Y) ≫ a.inv.app ((T.obj X).obj Y) ≫
        F'.map ((n.hom.app X).app Y) =
      (m.hom.app (F.obj X)).app (F.obj Y) ≫
        (U'.map (a.inv.app X)).app (M.obj (F.obj Y)) ≫
        (U'.obj (F'.obj (N.obj X))).map (a.inv.app Y) ≫
        (t'.inv.app (N.obj X)).app (N.obj Y) := by
  rw [← cancel_epi (M.map ((t.hom.app X).app Y)), ← M.map_comp_assoc,
    ← NatTrans.comp_app, Iso.hom_inv_id_app, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% (h X Y)]
  erw [(U'.map (a.inv.app X)).naturality_assoc]
  simp only [← NatTrans.comp_app_assoc, ← U'.map_comp, Iso.hom_inv_id_app]
  simp only [Functor.comp_obj]
  erw [Functor.map_id, Category.id_comp]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [Functor.map_id, Category.id_comp,
    ← NatTrans.comp_app, Iso.hom_inv_id_app, NatTrans.id_app, Category.comp_id]

private def mixedTensor
    {C D : Type*} [Category* C] [Category* D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D)
    {F G : C ⥤ D} (e : F ≅ G)
    (t : (postcompose₂.obj F).obj T ≅ (((whiskeringLeft₂ D).obj F).obj F).obj U) :
    (((whiskeringLeft₂ D).obj G).obj F).obj U ≅ (postcompose₂.obj G).obj T :=
  (((whiskeringLeft₂ D).mapIso e.symm).app F).app U ≪≫ t.symm ≪≫
    (postcompose₂.mapIso e).app T

private lemma mixed_tensor_square
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {F G : C ⥤ D} {F' G' : C' ⥤ D'} {N : C ⥤ C'} {M : D ⥤ D'}
    {T : C ⥤ C ⥤ C} {U : D ⥤ D ⥤ D}
    {T' : C' ⥤ C' ⥤ C'} {U' : D' ⥤ D' ⥤ D'}
    (a : N ⋙ F' ≅ F ⋙ M) (e : F ≅ G) (f : F' ≅ G')
    (t : (postcompose₂.obj F).obj T ≅ (((whiskeringLeft₂ D).obj F).obj F).obj U)
    (t' : (postcompose₂.obj F').obj T' ≅ (((whiskeringLeft₂ D').obj F').obj F').obj U')
    (m : (postcompose₂.obj M).obj U ≅ (((whiskeringLeft₂ D').obj M).obj M).obj U')
    (n : (postcompose₂.obj N).obj T ≅ (((whiskeringLeft₂ C').obj N).obj N).obj T')
    (h : Adjunction.ComparisonCompatible a t.hom t'.hom m n) (X Y : C) :
    M.map (((mixedTensor T U e t).hom.app X).app Y) ≫
      (isoWhiskerRight e.symm M ≪≫ a.symm ≪≫ isoWhiskerLeft N f).hom.app
        ((T.obj X).obj Y) ≫ G'.map ((n.hom.app X).app Y) =
    (m.hom.app (G.obj X)).app (F.obj Y) ≫
      (U'.map ((isoWhiskerRight e.symm M ≪≫ a.symm ≪≫
        isoWhiskerLeft N f).hom.app X)).app (M.obj (F.obj Y)) ≫
      (U'.obj (G'.obj (N.obj X))).map (a.inv.app Y) ≫
      ((mixedTensor T' U' f t').hom.app (N.obj X)).app (N.obj Y) := by
  simp only [mixedTensor, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    Iso.app_hom, Functor.mapIso_hom, whiskeringLeft₂_map_app_app_app_app,
    postcompose₂_map_app_app_app, Functor.map_comp, Category.assoc]
  have ce : M.map (e.hom.app ((T.obj X).obj Y)) ≫
      M.map (e.inv.app ((T.obj X).obj Y)) = 𝟙 _ := by
    rw [← M.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  rw [reassoc_of% ce, ← f.hom.naturality]
  rw [reassoc_of% (inverse_tensor_square a t t' m n h X Y)]
  have hm := NatTrans.congr_app (m.hom.naturality (e.inv.app X)) (F.obj Y)
  dsimp at hm
  rw [reassoc_of% hm]
  congr 3
  erw [(U'.map (f.inv.app (N.obj X))).naturality_assoc]
  simp only [← NatTrans.comp_app_assoc, ← U'.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  rfl

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The canonical comparison `A_U Lj_e^* ≅ Lj_p^* A_X`, with the exact derived
pullbacks identified with their total left derived functors. It is the degreewise
localization of the recorded section-normalized comparison, not a chosen isomorphism.
Source: Stacks Project, Tags 00WX and 0B65, and the blueprint finite-coefficient
transport paragraph (blueprint: lem-sf-comparison-open-tensor-coherence). -/
noncomputable def comparisonOpenDerivedPullbackIso
    (Λ : Type (u + 1)) [CommRing Λ] {U X : Scheme.{u}} (j : U ⟶ X) :
    L(Etale.upperStar (ModuleCat.{u + 1} Λ) j) ⋙
        D(comparisonUpperStar (ModuleCat.{u + 1} Λ) U) ≅
      D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X) ⋙
        L(upperStar (ModuleCat.{u + 1} Λ) j) :=
  Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j)
      D(comparisonUpperStar (ModuleCat.{u + 1} Λ) U) ≪≫
    Functor.mapDerivedCategoryCompIso
      (Etale.upperStar (ModuleCat.{u + 1} Λ) j)
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U) ≪≫
    Functor.mapDerivedCategoryNatIso
      (F := Etale.upperStar (ModuleCat.{u + 1} Λ) j ⋙
        comparisonUpperStar (ModuleCat.{u + 1} Λ) U)
      (G := comparisonUpperStar (ModuleCat.{u + 1} Λ) X ⋙
        upperStar (ModuleCat.{u + 1} Λ) j)
      (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j) ≪≫
    (Functor.mapDerivedCategoryCompIso
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
      (upperStar (ModuleCat.{u + 1} Λ) j)).symm ≪≫
    Functor.isoWhiskerLeft D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).symm

/-- The map `h_{K,N} = (1 ⊗ a_{j,N}) ∘ t_U` of the node. The tensor comparison is
that of the strong monoidal comparison pullback, computed on K-flat representatives;
`a` is the canonical comparison of pullbacks localized degreewise. These constructions
are natural in both inputs.
Source: Stacks Project, Tag 07A4, and the blueprint finite-coefficient transport
paragraph (blueprint: lem-sf-comparison-open-tensor-coherence). -/
noncomputable def comparisonOpenTensorIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {U X : Scheme.{u}} (j : U ⟶ X)
    (K : Etale.DerivedCategoryModule Λ U) (N : Etale.DerivedCategoryModule Λ X) :
    D(comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj
        (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) U).obj K).obj
          (L(Etale.upperStar (ModuleCat.{u + 1} Λ) j).obj N)) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
        (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj K)).obj
          (L(upperStar (ModuleCat.{u + 1} Λ) j).obj
            (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj N)) :=
  (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} Λ) K).app
        (L(Etale.upperStar (ModuleCat.{u + 1} Λ) j).obj N) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
      (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj K)).mapIso
        ((comparisonOpenDerivedPullbackIso Λ j).app N)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.flexible false in
private lemma restriction_mate (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (mateEquiv (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) j)
      (Etale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) j)
      (comparisonLowerStarOpenImmersionRestrictionIso (ModuleCat.{u + 1} Λ) j).hom) =
      (lowerStarCompComparisonLowerStarIso j (ModuleCat.{u + 1} Λ)).hom := by
  ext F : 2
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun W ↦ ?_)
  simp [mateEquiv, comparisonLowerStarOpenImmersionRestrictionIso,
    openImmersionRestrictionLowerStarAdjunction,
    Etale.openImmersionRestrictionLowerStarAdjunction,
    localizationRestrictionLowerStarAdjunction,
    Etale.localizationRestrictionLowerStarAdjunction,
    lowerStarCompComparisonLowerStarIso, comparisonLowerStar,
    openImmersionRestriction, Etale.openImmersionRestriction,
    localizationRestriction, Etale.localizationRestriction,
    lowerStar, Etale.lowerStar]
  erw [Category.id_comp, ← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  ext
  simp only [Quiver.Hom.unop_op, toProEtCompOverPullbackIso,
    NatIso.ofComponents_inv_app, Iso.refl_inv]
  apply CategoryTheory.Limits.pullback.hom_ext <;> simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private lemma comparison_restriction_mate (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (mateEquiv (comparisonAdjunction (ModuleCat.{u + 1} Λ) X)
      (comparisonAdjunction (ModuleCat.{u + 1} Λ) U)
      (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j).hom) =
      Functor.whiskerLeft (comparisonLowerStar (ModuleCat.{u + 1} Λ) X)
        (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ) j).hom ≫
      (comparisonLowerStarOpenImmersionRestrictionIso (ModuleCat.{u + 1} Λ) j).hom ≫
      Functor.whiskerRight
        (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ) j).inv
        (comparisonLowerStar (ModuleCat.{u + 1} Λ) U) := by
  let A := ModuleCat.{u + 1} Λ
  apply (mateEquiv (upperStarLowerStarAdjunction A j)
    (Etale.upperStarLowerStarAdjunction A j)).injective
  change (mateEquiv _ _ (mateEquiv _ _ _)) = _
  rw [iterated_mateEquiv_conjugateEquiv]
  have h := mateEquiv_leftAdjointUniq (upperStarLowerStarAdjunction A j)
    (openImmersionRestrictionLowerStarAdjunction A j)
    (Etale.upperStarLowerStarAdjunction A j)
    (Etale.openImmersionRestrictionLowerStarAdjunction A j)
    (TwoSquare.mk _ _ _ _ (comparisonLowerStarOpenImmersionRestrictionIso A j).hom)
  have hh := h
  change (mateEquiv (upperStarLowerStarAdjunction A j)
    (Etale.upperStarLowerStarAdjunction A j)
    (Functor.whiskerLeft (comparisonLowerStar A X)
        (Etale.upperStarIsoOpenImmersionRestriction A j).hom ≫
      (comparisonLowerStarOpenImmersionRestrictionIso A j).hom ≫
      Functor.whiskerRight (upperStarIsoOpenImmersionRestriction A j).inv
        (comparisonLowerStar A U))) = _ at hh
  rw [restriction_mate] at hh
  change _ = (mateEquiv (upperStarLowerStarAdjunction A j)
    (Etale.upperStarLowerStarAdjunction A j) _)
  rw [hh]
  exact Equiv.apply_symm_apply _ _

-- Bound the concrete adjunction comparison while diagnosing elaboration.
set_option backward.defeqAttrib.useBackward true in
private lemma comparison_extension_mate (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (mateEquiv (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j).inv) =
      (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j).hom := by
  let A := ModuleCat.{u + 1} Λ
  have hh := conjugate_comp_transport
    (Etale.openImmersionLowerShriekAdjunction A j) (comparisonAdjunction A X)
    (comparisonAdjunction A U) (openImmersionLowerShriekAdjunction A j)
    (Etale.upperStarIsoOpenImmersionRestriction A j).symm
    (upperStarIsoOpenImmersionRestriction A j).symm
    (openImmersionLowerShriekComparisonUpperStarIso A j).inv
    (comparisonLowerStarOpenImmersionRestrictionIso A j).hom
    (conjugate_inverse _ _ _)
  apply (mateEquiv (comparisonAdjunction A X) (comparisonAdjunction A U)).injective
  change (mateEquiv _ _ (mateEquiv _ _ _)) = _
  rw [iterated_mateEquiv_conjugateEquiv]
  exact hh.trans (comparison_restriction_mate Λ j).symm

noncomputable def comparisonTensorNatIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) :=
  tensorTransport (Etale.derivedTensor (ModuleCat.{u + 1} Λ) X)
    (derivedTensor (ModuleCat.{u + 1} Λ) X)
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).leftDerivedFunctorIsoMapDerivedCategory
    (asIso (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).leftDerivedTensorComparison)

-- Avoid unbounded unfolding while checking the two site comparisons.
lemma supportComparison_eq (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j =
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j).symm := by
  have h : supportSiteComparisonCoefficientDirectImageIso (ModuleCat.{u + 1} Λ) j =
      lowerStarCompComparisonLowerStarIso j (ModuleCat.{u + 1} Λ) := by
    apply Iso.ext
    apply NatTrans.ext
    funext F
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    simp only [supportSiteComparisonCoefficientDirectImageIso,
      lowerStarCompComparisonLowerStarIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.sheafPushforwardContinuousComp,
      Functor.sheafPushforwardContinuousIso,
      supportSiteComparisonSiteBaseChangeIso, toProEtCompOverPullbackIso,
      Iso.refl_hom, NatTrans.id_app]
    rfl
  change ((conjugateIsoEquiv _ _).symm
    (supportSiteComparisonCoefficientDirectImageIso (ModuleCat.{u + 1} Λ) j).symm).symm = _
  rw [h]
  rfl

private lemma comparisonPullback_transport (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    Functor.isoWhiskerRight
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).leftDerivedFunctorIsoMapDerivedCategory.symm
        L(upperStar (ModuleCat.{u + 1} Λ) j) ≪≫
      leftDerivedComparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j ≪≫
      Functor.isoWhiskerLeft L(Etale.upperStar (ModuleCat.{u + 1} Λ) j)
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).leftDerivedFunctorIsoMapDerivedCategory =
      (comparisonOpenDerivedPullbackIso Λ j).symm := by
  have hd : Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j).symm =
      (Functor.mapDerivedCategoryNatIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j)).symm :=
    Iso.ext (Functor.mapDerivedCategoryNatIso_symm _)
  apply Iso.ext
  apply NatTrans.ext
  funext N
  simp only [leftDerivedComparisonUpperStarCompUpperStarIso,
    Functor.leftDerivedFunctorCompNatIso, Functor.leftDerivedFunctorCompIso,
    Functor.leftDerivedFunctorNatIso, comparisonOpenDerivedPullbackIso,
    supportComparison_eq, hd, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc,
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
    leftDerivedUpperStarIsoMapDerivedCategory, Etale.leftDerivedUpperStarIsoMapDerivedCategory]
  rw [← NatTrans.naturality_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

lemma comparison_tensor_compatible
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    Adjunction.ComparisonCompatible (comparisonOpenDerivedPullbackIso Λ j).symm
      (Etale.leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) j)
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) j)
      (comparisonTensorNatIso Λ U) (comparisonTensorNatIso Λ X) := by
  have h := comparisonCompatible_transport
    (leftDerivedComparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j)
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).leftDerivedFunctorIsoMapDerivedCategory
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).leftDerivedFunctorIsoMapDerivedCategory
    (Etale.leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) j)
    (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) j)
    (asIso (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).leftDerivedTensorComparison)
    (asIso (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).leftDerivedTensorComparison)
    (comparisonCompatible_leftDerivedComparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} Λ) j)
  rw [comparisonPullback_transport] at h
  exact h

private lemma tensorTransport_app
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D)
    {F G : C ⥤ D} (e : F ≅ G)
    (m : (Functor.postcompose₂.obj F).obj T ≅
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj U) (K : C) :
    (tensorTransport T U e m).app K =
      Functor.isoWhiskerLeft (T.obj K) e.symm ≪≫ m.app K ≪≫
        Functor.isoWhiskerRight e (U.obj (F.obj K)) ≪≫
        Functor.isoWhiskerLeft G (U.mapIso (e.app K)) := by
  rfl

lemma comparison_tensor_app (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (X : Scheme.{u}) (K : Etale.DerivedCategoryModule Λ X) :
    (comparisonTensorNatIso Λ X).app K =
      derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} Λ) K := by
  exact tensorTransport_app _ _ _ _ _

-- Bound the comparison of the two composite isomorphisms.
private lemma comparison_mixed_pullback (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    Functor.isoWhiskerRight
        (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).symm
        D(comparisonUpperStar (ModuleCat.{u + 1} Λ) U) ≪≫
      comparisonOpenDerivedPullbackIso Λ j ≪≫
      Functor.isoWhiskerLeft D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j) =
    Functor.mapDerivedCategorySquareIso
      (F₁ := Etale.upperStar (ModuleCat.{u + 1} Λ) j)
      (F₂ := comparisonUpperStar (ModuleCat.{u + 1} Λ) U)
      (G₁ := comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
      (G₂ := upperStar (ModuleCat.{u + 1} Λ) j)
      (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j) := by
  ext N
  simp only [comparisonOpenDerivedPullbackIso, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
-- Keep localization elaboration within a fixed bound.
private lemma comparison_derived_extension_mate (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : Etale.DerivedCategoryModule Λ U) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
        (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj K) ≫
      D(upperStar (ModuleCat.{u + 1} Λ) j).map
        ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} Λ) j).inv.app K) =
    D(comparisonUpperStar (ModuleCat.{u + 1} Λ) U).map
        ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} Λ) j).unit.app K) ≫
      (Functor.mapDerivedCategorySquareIso
        (F₁ := Etale.upperStar (ModuleCat.{u + 1} Λ) j)
        (F₂ := comparisonUpperStar (ModuleCat.{u + 1} Λ) U)
        (G₁ := comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
        (G₂ := upperStar (ModuleCat.{u + 1} Λ) j)
        (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j)).hom.app
          (D(Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj K) := by
  let A := ModuleCat.{u + 1} Λ
  have hβ (F : Sheaf U.smallEtaleTopology A) :=
    unit_of_mate (Etale.openImmersionLowerShriekUpperStarAdjunction A j)
      (openImmersionLowerShriekUpperStarAdjunction A j)
      (openImmersionLowerShriekComparisonUpperStarIso A j).inv
      (supportSiteComparisonCoefficientPullbackIso A j).hom
      (comparison_extension_mate Λ j) F
  have h := Adjunction.mapDerivedCategoryAdjunction_mate
    (Etale.openImmersionLowerShriekUpperStarAdjunction A j)
    (openImmersionLowerShriekUpperStarAdjunction A j)
    (u := comparisonUpperStar A U) (v := comparisonUpperStar A X)
    (supportSiteComparisonCoefficientPullbackIso A j)
    (openImmersionLowerShriekComparisonUpperStarIso A j).symm hβ K
  dsimp [A] at h ⊢
  simpa only [derivedOpenImmersionLowerShriekUpperStarAdjunction,
    Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction,
    Functor.mapDerivedCategorySquareIso,
    mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.mapDerivedCategoryNatIso_symm, Category.assoc] using h

private lemma comparison_mixed_tensor_compatible
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P Q : Etale.DerivedCategoryModule Λ X) :
    D(comparisonUpperStar (ModuleCat.{u + 1} Λ) U).map
        (((Etale.mapDerivedCategoryUpperStarDerivedTensorIso
          (ModuleCat.{u + 1} Λ) j).hom.app P).app Q) ≫
      (Functor.mapDerivedCategorySquareIso
        (F₁ := Etale.upperStar (ModuleCat.{u + 1} Λ) j)
        (F₂ := comparisonUpperStar (ModuleCat.{u + 1} Λ) U)
        (G₁ := comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
        (G₂ := upperStar (ModuleCat.{u + 1} Λ) j)
        (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j)).hom.app
          (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj P).obj Q) ≫
      D(upperStar (ModuleCat.{u + 1} Λ) j).map
        (((comparisonTensorNatIso Λ X).hom.app P).app Q) =
    ((comparisonTensorNatIso Λ U).hom.app
        (D(Etale.upperStar (ModuleCat.{u + 1} Λ) j).obj P)).app
          (L(Etale.upperStar (ModuleCat.{u + 1} Λ) j).obj Q) ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) U).map
        ((Functor.mapDerivedCategorySquareIso
          (F₁ := Etale.upperStar (ModuleCat.{u + 1} Λ) j)
          (F₂ := comparisonUpperStar (ModuleCat.{u + 1} Λ) U)
          (G₁ := comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
          (G₂ := upperStar (ModuleCat.{u + 1} Λ) j)
          (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j)).hom.app P)).app
            (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj
              (L(Etale.upperStar (ModuleCat.{u + 1} Λ) j).obj Q)) ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
        (D(upperStar (ModuleCat.{u + 1} Λ) j).obj
          (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj P))).map
            ((comparisonOpenDerivedPullbackIso Λ j).hom.app Q) ≫
      (((mapDerivedCategoryUpperStarDerivedTensorIso
        (ModuleCat.{u + 1} Λ) j).hom.app
          (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj P)).app
            (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj Q)) := by
  have h := mixed_tensor_square
    (comparisonOpenDerivedPullbackIso Λ j).symm
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j)
    (Etale.leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} Λ) j)
    (leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} Λ) j)
    (comparisonTensorNatIso Λ U) (comparisonTensorNatIso Λ X)
    (comparison_tensor_compatible Λ j) P Q
  simp only [Iso.symm_symm_eq, Iso.symm_inv] at h
  rw [comparison_mixed_pullback] at h
  exact h

/-- The comparison carries the canonical etale open tensor map to the pro-etale
one, for arbitrary unbounded `K` and `N`, naturally in both variables. In diagrammatic
composition order the equality is `A_X(γe) ≫ e ≫ j_!(h) = t_X ≫ (e ⊗ 1) ≫ γp`.
Source: Stacks Project, Tags 0GL1, 0E8I and 07A4, and the finite-coefficient
transport paragraph of `thm-sf-pf-proetale`
(blueprint: lem-sf-comparison-open-tensor-coherence).

Proof:
1. Compute the mate of the literal open-restriction square and transport it through
   the canonical identifications of restriction with pullback. The resulting square
   is the recorded support-site comparison; its left mate is the inverse extension
   comparison.
2. Localize the unit equation with `mapDerivedCategoryAdjunction_mate`, obtaining
   the mate equation for the termwise derived functors.
3. Transport the tensor compatibility of
   `leftDerivedComparisonUpperStarCompUpperStarIso` through the exact-functor
   identifications `L ≅ D`. Invert the tensorators and identify the first pullback
   argument with its termwise derived functor. This gives compatibility with the
   precise mixed tensorators defining both open projection maps.
4. Apply `Adjunction.projectionMap_mate`. Cancel the extension comparison and both
   projection isomorphisms; functoriality identifies the remaining two factors with
   `comparisonOpenTensorIso`. All inputs are arbitrary unbounded objects. -/
theorem comparison_open_tensor_coherence
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : Etale.DerivedCategoryModule Λ U) (N : Etale.DerivedCategoryModule Λ X) :
    D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X).map
        (((Etale.derivedOpenImmersionLowerShriekProjectionIso
          (ModuleCat.{u + 1} Λ) j).inv.app K).app N) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} Λ) j).hom.app
          (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) U).obj K).obj
            (L(Etale.upperStar (ModuleCat.{u + 1} Λ) j).obj N)) ≫
      D(openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).map
        (comparisonOpenTensorIso Λ j K N).hom =
    (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} Λ)
        (D(Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).obj K)).hom.app N ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).map
        ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} Λ) j).hom.app K)).app
            (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj N) ≫
      ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} Λ) j).inv.app
        (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj K)).app
          (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj N) := by
  have h := Adjunction.projectionMap_mate
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
    L(Etale.upperStar (ModuleCat.{u + 1} Λ) j) L(upperStar (ModuleCat.{u + 1} Λ) j)
    (Etale.mapDerivedCategoryUpperStarDerivedTensorIso (ModuleCat.{u + 1} Λ) j).hom
    (mapDerivedCategoryUpperStarDerivedTensorIso (ModuleCat.{u + 1} Λ) j).hom
    (comparisonTensorNatIso Λ U).hom (comparisonTensorNatIso Λ X).hom
    (Functor.mapDerivedCategorySquareIso
      (F₁ := Etale.upperStar (ModuleCat.{u + 1} Λ) j)
      (F₂ := comparisonUpperStar (ModuleCat.{u + 1} Λ) U)
      (G₁ := comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
      (G₂ := upperStar (ModuleCat.{u + 1} Λ) j)
      (supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} Λ) j)).hom
    (comparisonOpenDerivedPullbackIso Λ j).hom
    (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
      (ModuleCat.{u + 1} Λ) j).inv
    (comparison_derived_extension_mate Λ j)
    (comparison_mixed_tensor_compatible Λ j) K N
  change _ ≫ D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X).map
    (((Etale.derivedOpenImmersionLowerShriekProjectionIso
      (ModuleCat.{u + 1} Λ) j).hom.app K).app N) ≫ _ = _ at h
  simp only [← Iso.app_hom] at h
  simp only [comparison_tensor_app, Iso.app_hom] at h
  rw [← cancel_epi (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X).map
    (((Etale.derivedOpenImmersionLowerShriekProjectionIso
      (ModuleCat.{u + 1} Λ) j).hom.app K).app N)),
    ← Functor.map_comp_assoc, ← NatTrans.comp_app, Iso.hom_inv_id_app,
    NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← cancel_epi ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
    (ModuleCat.{u + 1} Λ) j).inv.app _)]
  erw [Iso.inv_hom_id_app_assoc]
  erw [reassoc_of% h]
  have ce :
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).map
        ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} Λ) j).inv.app K)).app
            (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj N) ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).map
        ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} Λ) j).hom.app K)).app
            (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj N) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, NatTrans.id_app]
  simp only [comparisonOpenTensorIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp]
  rw [reassoc_of% ce]
  change _ = _ ≫ _ ≫
    (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} Λ) j).hom.app
      (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj K)).app
        (D(comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj N)) ≫ _
  rw [← NatTrans.comp_app, Iso.hom_inv_id_app, NatTrans.id_app, Category.comp_id]

end AlgebraicGeometry.ProEtale
