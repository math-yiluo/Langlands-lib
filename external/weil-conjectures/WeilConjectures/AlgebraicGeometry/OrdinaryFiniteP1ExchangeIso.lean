/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows

/-! # Invertibility of the specified ordinary projective-line exchange

Source: Stacks Tag 0DDE; comparison of exact and left-derived mates
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

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

namespace Etale

/-- Proper exchange for the exact-mate presentation used by the ordinary finite P1 arrows.
Source: Stacks Tag 0DDE and the canonical mate transport along exact inverse image
(auxiliary; not a blueprint node).

Proof: projective space is proper over every scheme. A finite ring is additively
torsion, so the unbounded torsion-ring proper-base-change theorem makes its derived
exchange invertible. Transport the mate along the canonical isomorphisms from
left-derived inverse image to exact termwise inverse image. Conjugation changes its
right adjoints only by isomorphisms, hence preserves invertibility. The specified
ordinaryFiniteP1Exchange is this exact mate composed with the invertible endpoint
comparisons. No condition on the change of base, or on the coefficient complex, is used. -/
theorem isIso_ordinaryFiniteP1Exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S' S : Scheme.{u}} (g : S' ⟶ S)
    (M : DerivedCategoryModule A (ProjectiveLine S)) :
    IsIso (ordinaryFiniteP1Exchange A g M) := by
  have : IsProper (ProjectiveLine S ↘ S) :=
    ProjectiveSpace.instIsProper (ULift.{u} (Fin 2)) S
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring A
    isAddTorsion_of_finite (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g)
  have := (isIso_derived_exchange_iff_exact A
    (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).toCommSq M).mp
      (inferInstance : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} A)
        (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).toCommSq).app M))
  unfold ordinaryFiniteP1Exchange
  infer_instance

end Etale
end AlgebraicGeometry
