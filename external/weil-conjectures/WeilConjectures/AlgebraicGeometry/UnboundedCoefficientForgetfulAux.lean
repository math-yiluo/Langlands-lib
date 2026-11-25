/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

@[expose] public section

universe u

open CategoryTheory Limits

private lemma mate_whiskerTop
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G G' : A ⥤ C} {H : B ⥤ D}
    (α : TwoSquare G' L₁ L₂ H) (γ : G ⟶ G') (K : B) :
    (mateEquiv adj₁ adj₂ (α.whiskerTop γ)).app K =
      γ.app (R₁.obj K) ≫ (mateEquiv adj₁ adj₂ α).app K := by
  simp [mateEquiv, TwoSquare.whiskerTop]

private lemma mate_whiskerBottom
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G : A ⥤ C} {H H' : B ⥤ D}
    (α : TwoSquare G L₁ L₂ H) (δ : H ⟶ H') (K : B) :
    (mateEquiv adj₁ adj₂ (α.whiskerBottom δ)).app K =
      (mateEquiv adj₁ adj₂ α).app K ≫ R₂.map (δ.app K) := by
  simp [mateEquiv, TwoSquare.whiskerBottom, ← Functor.map_comp, δ.naturality]

-- Transporting either adjunction conjugates the mate by isomorphisms of right adjoints.
private lemma isIso_mate_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    {L₁' : A ⥤ B} {R₁' : B ⥤ A} {L₂' : C ⥤ D} {R₂' : D ⥤ C}
    (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
    (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂') (eG : G' ≅ G) (eH : H ≅ H')
    (α : TwoSquare G L₁ L₂ H) (K : B) :
    IsIso ((mateEquiv adj₁' adj₂'
      ((((α.whiskerTop eG.hom).whiskerBottom eH.hom).whiskerRight e₂.inv).whiskerLeft
        e₁.hom)).app K) ↔ IsIso ((mateEquiv adj₁ adj₂ α).app K) := by
  rw [conjugateEquiv_mateEquiv_vcomp adj₁' adj₁ adj₂',
    mateEquiv_conjugateEquiv_vcomp adj₁ adj₂ adj₂']
  simp only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
    isIso_comp_left_iff, isIso_comp_right_iff]
  rw [mate_whiskerBottom, mate_whiskerTop]
  simp only [isIso_comp_left_iff, isIso_comp_right_iff]

namespace AlgebraicGeometry
open Scheme

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

-- Only invertibility is needed, so arbitrary adjunctions on the two isomorphic left
-- adjoints suffice: the conjugate right-adjoint comparisons are automatically invertible.
private theorem isIso_derived_exchange_iff_exact
    (Λ : Type (u + 1)) [CommRing Λ] (sq : CommSq g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((Etale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app K) ↔
      IsIso ((Etale.exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app K) := by
  let A := ModuleCat.{u + 1} Λ
  let α := TwoSquare.mk _ _ _ _ (Etale.exactDerivedSquareUpperStarIso A sq).hom
  have h := isIso_mate_transport
    (Etale.mapDerivedUpperStarLowerStarAdjunction A f)
    (Etale.mapDerivedUpperStarLowerStarAdjunction A f')
    (Etale.derivedUpperStarLowerStarAdjunction A f)
    (Etale.derivedUpperStarLowerStarAdjunction A f')
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory A f).symm
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory A f').symm
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory A g)
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory A g').symm α K
  have hs :
      ((((α.whiskerTop (Etale.leftDerivedUpperStarIsoMapDerivedCategory A g).hom).whiskerBottom
        (Etale.leftDerivedUpperStarIsoMapDerivedCategory A g').inv).whiskerRight
        (Etale.leftDerivedUpperStarIsoMapDerivedCategory A f').hom).whiskerLeft
        (Etale.leftDerivedUpperStarIsoMapDerivedCategory A f).inv) =
      TwoSquare.mk _ _ _ _ (Etale.derivedSquareUpperStarIso A sq).hom := by
    ext M
    simp only [α, TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
      TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.mk]
    simp only [Etale.derivedSquareUpperStarIso, Etale.leftDerivedUpperStarComp,
      Etale.exactDerivedSquareUpperStarIso, Etale.squareUpperStarIso,
      Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
      Etale.leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Category.assoc,
      Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
      Iso.inv_hom_id_app_assoc]
    rw [← (Etale.upperStar A g').leftDerivedFunctorIsoMapDerivedCategory.inv.naturality]
  simp only [Iso.symm_hom, Iso.symm_inv] at h
  rw [hs] at h
  exact h

-- Cancel the invertible endpoint comparisons in the existing exchange equation.
private theorem isIso_exact_exchange_iff_abelian
    (Λ : Type (u + 1)) [CommRing Λ]
    (sq : ChosenCartesianSquare g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((Etale.exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) ↔
      IsIso ((Etale.exactDerivedBaseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app
        ((Etale.moduleAbelianForget Λ X).mapDerivedCategory.obj K)) := by
  obtain ⟨hU, hR, hEx⟩ := Etale.unbounded_abelian_exchange_comparison Λ sq
  have := (hU Y').2.2.2.1
  have := (hR f).1
  have := (hR f').1
  rw [← isIso_iff_of_reflects_iso _ (Etale.moduleAbelianForget Λ Y').mapDerivedCategory]
  have h := hEx K
  have hi := congrArg IsIso h
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hi.to_iff

-- The underlying sheaf functors agree definitionally; localization supplies the iso.
private noncomputable def restrictScalarsForgetIso
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S)
    (T : Scheme.{u}) :
    CategoryTheory.Sheaf.derivedRestrictScalars T.smallEtaleTopology φ ⋙
        (Etale.moduleAbelianForget R T).mapDerivedCategory ≅
      (Etale.moduleAbelianForget S T).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (show CategoryTheory.Sheaf.restrictScalars T.smallEtaleTopology φ ⋙
          Etale.moduleAbelianForget R T ≅ Etale.moduleAbelianForget S T from Iso.refl _)

/-- Restriction of scalars preserves the invertibility test for the canonical unbounded
exchange, after identifying its source and target with the restricted-coefficient versions.
Source: Stacks Project, Tag 0D6J(3), and the canonical mate coherence of
`lem-kun-unbounded-abelian-exchange-comparison`.
(auxiliary; not a blueprint node)

Proof in words: write U_R and U_S for forgetting R- and S-module structure to abelian
sheaves. Termwise restriction gives U_R Res = U_S, including on complexes and their
localizations. Inverse-image commutes with this identification. For direct images,
Tag 0D6J(3) gives canonical isomorphisms from the forgotten unbounded derived direct
images to the abelian derived direct image. The canonical mate coherence of
lem-kun-unbounded-abelian-exchange-comparison identifies both forgotten exchange
morphisms with the same abelian exchange, conjugated by their invertible endpoint
comparisons. Hence one forgotten exchange is invertible exactly when the other is.
Forgetting R-module structure reflects isomorphisms, because homology commutes with
this exact functor and isomorphisms of sheaves are tested sectionwise. Applying this
test to the two R-derived morphisms gives the stated equivalence. No cyclic-coefficient,
properness, flatness, boundedness, or exchange-invertibility hypothesis is used. -/
theorem isIso_restricted_derivedBaseChangeMap_iff
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S)
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S))) :
    IsIso ((CategoryTheory.Sheaf.derivedRestrictScalars Y'.smallEtaleTopology φ).map
      ((Etale.derivedBaseChangeMap (ModuleCat.{u + 1} S) sq.toCommSq).app K)) ↔
    IsIso ((Etale.derivedBaseChangeMap (ModuleCat.{u + 1} R) sq.toCommSq).app
      ((CategoryTheory.Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj K)) := by
  let c : ChosenCartesianSquare g' f' f g :=
    { toCommSq := sq.toCommSq
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd }
  have := ((Etale.unbounded_abelian_exchange_comparison R c).1 Y').2.2.2.1
  have := ((Etale.unbounded_abelian_exchange_comparison S c).1 Y').2.2.2.1
  let a := (Etale.derivedBaseChangeMap (ModuleCat.{u + 1} S) sq.toCommSq).app K
  have hres :
      IsIso ((CategoryTheory.Sheaf.derivedRestrictScalars Y'.smallEtaleTopology φ).map a) ↔
        IsIso a :=
    (isIso_iff_of_reflects_iso _ (Etale.moduleAbelianForget R Y').mapDerivedCategory).symm.trans
      ((NatIso.isIso_map_iff (restrictScalarsForgetIso φ Y') a).trans
        (isIso_iff_of_reflects_iso a (Etale.moduleAbelianForget S Y').mapDerivedCategory))
  rw [hres, isIso_derived_exchange_iff_exact S,
    isIso_derived_exchange_iff_exact R]
  exact (isIso_exact_exchange_iff_abelian S c K).trans
    ((NatTrans.isIso_app_iff_of_iso
      (Etale.exactDerivedBaseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq)
      ((restrictScalarsForgetIso φ X).app K)).symm.trans
      (isIso_exact_exchange_iff_abelian R c _).symm)

end AlgebraicGeometry
