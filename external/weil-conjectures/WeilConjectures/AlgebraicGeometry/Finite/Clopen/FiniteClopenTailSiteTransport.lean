/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenMateData
public import WeilConjectures.AlgebraicGeometry.ClopenMateNormalization.EtaleClopenMateNormalization
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique

/-! # Site comparison for the clopen projection and compositors

Source: Stacks Project, Tags 09AF and 0F7B.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible] CategoryTheory.Functor.leftAdjoint

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

open CategoryTheory.Functor

-- These mate-transport calculations are the ordinary-sheaf part of the proof in
-- WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence,
-- with no tensor or derived functors.
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

-- Restricting either canonical clopen projector gives the open-adjunction unit.
namespace EtaleProjection

open AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ]

private theorem etale_projection_restrict {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) s).map
        ((Etale.ClopenMateNormalization.projection Λ s).app F) =
      (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) s).unit.app
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) s).obj F) := by
  have := Etale.isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
    (ModuleCat.{u + 1} Λ) s s.isClosedEmbedding.isClosed_range
  apply (cancel_mono
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) s).map
        ((Etale.openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) s).app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) s).obj F)) ≫
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).counit.app _)).1
  rw [Etale.unit_map_openImmersionLowerShriekToLowerStar_app_counit]
  simp only [Etale.ClopenMateNormalization.projection, NatTrans.comp_app, Functor.whiskerLeft_app,
    CategoryTheory.Functor.map_comp, Category.assoc]
  simp only [NatIso.isIso_inv_app]
  simp only [CategoryTheory.Functor.map_inv, IsIso.inv_hom_id_assoc]
  exact (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).left_triangle_components F

end EtaleProjection

private lemma pro_unit_toStar
    (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ)) :
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app F ≫
        (upperStar (ModuleCat.{u + 1} Λ) j).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j).app F) ≫
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app F = 𝟙 F := by
  have hc := (Adjunction.leftAdjointUniq_hom_app_counit
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j)
    (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) j) F).symm
  change (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app F =
    (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ) j).hom.app _ ≫
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app F
    at hc
  change ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} Λ) j).unit.app F ≫
    (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} Λ) j).inv.app _) ≫ _ ≫ _ = _
  rw [hc, Category.assoc, NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc,
    openImmersionLowerShriekToLowerStar_app, Functor.map_comp, Category.assoc]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [Adjunction.unit_naturality_assoc, Adjunction.right_triangle_components_assoc]
  simp

private theorem pro_projection_restrict
    (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    (upperStar (ModuleCat.{u + 1} Λ) s).map ((cbcClopenProjection Λ s).app F) =
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) s).unit.app
        ((upperStar (ModuleCat.{u + 1} Λ) s).obj F) := by
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
    (ModuleCat.{u + 1} Λ) s s.isClosedEmbedding.isClosed_range
  have hc := (Adjunction.leftAdjointUniq_hom_app_counit
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s)
    (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) s)
    ((upperStar (ModuleCat.{u + 1} Λ) s).obj F)).symm
  have : IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).counit.app
      ((upperStar (ModuleCat.{u + 1} Λ) s).obj F)) := by
    rw [hc]
    infer_instance
  apply (cancel_mono
    ((upperStar (ModuleCat.{u + 1} Λ) s).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) s).app
          ((upperStar (ModuleCat.{u + 1} Λ) s).obj F)) ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).counit.app _)).1
  rw [pro_unit_toStar]
  simp only [cbcClopenProjection, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  simp only [NatIso.isIso_inv_app]
  simp only [Functor.map_inv, IsIso.inv_hom_id_assoc]
  exact (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).left_triangle_components F

-- The adjunction detects maps into direct image, hence into clopen extension by zero.
private lemma map_to_right_adjoint_injective
    {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {X Y : C} {Z : D} (e : Y ≅ R.obj Z) {f g : X ⟶ Y}
    (h : L.map f = L.map g) : f = g := by
  apply (cancel_mono e.hom).1
  apply (a.homEquiv X Z).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, h]

private lemma pullback_comparison_eq (Λ : Type (u + 1)) [CommRing Λ]
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

private theorem clopen_projection_comparison
    (Λ : Type (u + 1)) [CommRing Λ]
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).map
        ((Etale.ClopenMateNormalization.projection Λ s).app F) ≫
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) s).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) s).obj F) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).map
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) s).inv.app F) =
    (cbcClopenProjection Λ s).app
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).obj F) := by
  let A := ModuleCat.{u + 1} Λ
  let E := (Etale.upperStar A s).obj F
  let o := openImmersionLowerShriekComparisonUpperStarIso A s
  let a := comparisonUpperStarCompUpperStarIso A s
  have hu := unit_mateEquiv
    (Etale.openImmersionLowerShriekUpperStarAdjunction A s)
    (openImmersionLowerShriekUpperStarAdjunction A s) o.inv E
  change (comparisonUpperStar A U).map
      ((Etale.openImmersionLowerShriekUpperStarAdjunction A s).unit.app E) ≫
      ((mateEquiv (Etale.openImmersionLowerShriekUpperStarAdjunction A s)
        (openImmersionLowerShriekUpperStarAdjunction A s) o.inv)).app
          ((Etale.openImmersionLowerShriek A s).obj E) =
    (openImmersionLowerShriekUpperStarAdjunction A s).unit.app
      ((comparisonUpperStar A U).obj E) ≫
      (upperStar A s).map (o.inv.app E) at hu
  rw [comparison_extension_mate, pullback_comparison_eq] at hu
  have hi := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
    A s s.isClosedEmbedding.isClosed_range
  apply map_to_right_adjoint_injective (upperStarLowerStarAdjunction A s)
    (asIso ((openImmersionLowerShriekToLowerStar A s).app _))
  simp only [Functor.map_comp]
  rw [pro_projection_restrict]
  apply (cancel_epi (a.inv.app F)).1
  have hn := a.inv.naturality ((Etale.ClopenMateNormalization.projection Λ s).app F)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [EtaleProjection.etale_projection_restrict]
  dsimp only [A, E, o, a] at *
  simp only [Iso.symm_hom] at hu
  rw [reassoc_of% hu]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj]
  rw [(upperStar A s).map_id, Category.id_comp]
  have hnunit := (openImmersionLowerShriekUpperStarAdjunction A s).unit.naturality
    ((comparisonUpperStarCompUpperStarIso A s).inv.app F)
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hnunit
  exact hnunit.symm

-- Invert the existing coherence squares and retain the specified equality transports.
private theorem open_compositor_comparison
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U P X : Scheme.{u}} (s : U ⟶ P) (b : P ⟶ X) (k : U ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] [IsOpenImmersion k] (hk : s ≫ b = k)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).map
        (((Etale.openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) s b).inv ≫
          (Etale.ClopenMateNormalization.openCongr Λ hk).hom).app F) ≫
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) k).hom.app F =
    (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) b).hom.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).obj F) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b).map
        ((openImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} Λ) s).hom.app F) ≫
      ((proEtaleOpenExtensionComp Λ s b).inv ≫ (cbcOpenCongr Λ hk).hom).app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj F) := by
  subst k
  simp only [Etale.ClopenMateNormalization.openCongr, cbcOpenCongr,
    Iso.refl_hom, Category.comp_id]
  let A := ModuleCat.{u + 1} Λ
  have hc := (openImmersionLowerShriekComparison_coherence Λ).2.1 s b F
  apply (cancel_epi ((comparisonUpperStar A X).map
    ((Etale.openImmersionLowerShriekComp A s b).hom.app F))).1
  dsimp only [A] at *
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact hc.symm

private theorem pull_compositor_comparison
    (Λ : Type (u + 1)) [CommRing Λ]
    {U P S : Scheme.{u}} (s : U ⟶ P) (q : P ⟶ S) (r : U ⟶ S) (hr : s ≫ q = r)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).map
        (((Etale.upperStarComp (ModuleCat.{u + 1} Λ) s q).inv ≫
          (eqToIso (congrArg (Etale.upperStar (ModuleCat.{u + 1} Λ)) hr)).hom).app F) ≫
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) r).inv.app F =
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) s).inv.app
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) q).obj F) ≫
      (upperStar (ModuleCat.{u + 1} Λ) s).map
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) q).inv.app F) ≫
      ((upperStarComp (ModuleCat.{u + 1} Λ) s q).inv ≫
        (cbcPullCongr Λ hr).hom).app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) S).obj F) := by
  subst r
  simp only [eqToIso_refl, cbcPullCongr, Iso.refl_hom, Category.comp_id]
  let A := ModuleCat.{u + 1} Λ
  have hc := (comparison_pullback_coherent.2.2 Λ).2.1 U P S s q F
  change (comparisonUpperStar A U).map ((Etale.upperStarComp A s q).hom.app F) ≫
      (comparisonUpperStarCompUpperStarIso A s).inv.app
        ((Etale.upperStar A q).obj F) ≫
      (upperStar A s).map ((comparisonUpperStarCompUpperStarIso A q).inv.app F) =
    (comparisonUpperStarCompUpperStarIso A (s ≫ q)).inv.app F ≫
      (upperStarComp A s q).hom.app ((comparisonUpperStar A S).obj F) at hc
  apply (cancel_epi ((comparisonUpperStar A U).map
    ((Etale.upperStarComp A s q).hom.app F))).1
  dsimp only [A] at *
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% hc]
  simp only [Iso.hom_inv_id_app, Category.comp_id]

-- Paste the projection square and the two outgoing compositor squares.
private theorem tail_paste
    {C D E H C' D' E' H' : Type*}
    [Category* C] [Category* D] [Category* E] [Category* H]
    [Category* C'] [Category* D'] [Category* E'] [Category* H']
    {A : C ⥤ C'} {B : D ⥤ D'} {M : E ⥤ E'} {N : H ⥤ H'}
    {Q : C ⥤ D} {S : D ⥤ E} {R : C ⥤ E}
    {J : E ⥤ D} {T : D ⥤ H} {K : E ⥤ H}
    {Q' : C' ⥤ D'} {S' : D' ⥤ E'} {R' : C' ⥤ E'}
    {J' : E' ⥤ D'} {T' : D' ⥤ H'} {K' : E' ⥤ H'}
    (aq : Q ⋙ B ≅ A ⋙ Q') (as : S ⋙ M ≅ B ⋙ S') (ar : R ⋙ M ≅ A ⋙ R')
    (os : J ⋙ B ≅ M ⋙ J') (ob : T ⋙ N ≅ B ⋙ T') (ok : K ⋙ N ≅ M ⋙ K')
    (π : 𝟭 D ⟶ S ⋙ J) (π' : 𝟭 D' ⟶ S' ⋙ J')
    (cJ : J ⋙ T ⟶ K) (cJ' : J' ⋙ T' ⟶ K')
    (cG : Q ⋙ S ⟶ R) (cG' : Q' ⋙ S' ⟶ R')
    (hπ : ∀ X, B.map (π.app X) ≫ os.hom.app (S.obj X) ≫ J'.map (as.hom.app X) =
      π'.app (B.obj X))
    (hJ : ∀ X, N.map (cJ.app X) ≫ ok.hom.app X =
      ob.hom.app (J.obj X) ≫ T'.map (os.hom.app X) ≫ cJ'.app (M.obj X))
    (hG : ∀ X, M.map (cG.app X) ≫ ar.hom.app X =
      as.hom.app (Q.obj X) ≫ S'.map (aq.hom.app X) ≫ cG'.app (A.obj X)) (F : C) :
    N.map (T.map (π.app (Q.obj F)) ≫ cJ.app (S.obj (Q.obj F)) ≫ K.map (cG.app F)) ≫
      ok.hom.app (R.obj F) ≫ K'.map (ar.hom.app F) =
    ob.hom.app (Q.obj F) ≫ T'.map (aq.hom.app F) ≫
      T'.map (π'.app (Q'.obj (A.obj F))) ≫
      cJ'.app (S'.obj (Q'.obj (A.obj F))) ≫ K'.map (cG'.app (A.obj F)) := by
  simp only [Functor.map_comp, Category.assoc]
  have nk := ok.hom.naturality (cG.app F)
  have nb := ob.hom.naturality (π.app (Q.obj F))
  simp only [Functor.comp_map] at nk nb
  rw [reassoc_of% nk, reassoc_of% hJ, reassoc_of% nb]
  rw [← K'.map_comp, hG]
  simp only [Functor.map_comp]
  have nj := cJ'.naturality (as.hom.app (Q.obj F))
  simp only [Functor.comp_map] at nj
  rw [← reassoc_of% nj]
  rw [← T'.map_comp_assoc, ← T'.map_comp_assoc]
  simp only [Category.assoc]
  rw [hπ]
  have nj' := cJ'.naturality (S'.map (aq.hom.app F))
  have np := π'.naturality (aq.hom.app F)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at nj' np
  rw [← reassoc_of% nj', ← T'.map_comp_assoc, ← np]
  simp only [Functor.map_comp, Category.assoc]

/-- The part of the proetale alpha after cartesian base change.
Source: Stacks Tags 09AF and 0F7B
(blueprint: lem-cbc-finite-clopen-tail-site-transport). -/
def finiteClopenProEtaleTail
    (Λ : Type (u + 1)) [CommRing Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    upperStar (ModuleCat.{u + 1} Λ) (pullback.snd p i) ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (pullback.fst p i) ⟶
      upperStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k :=
  Functor.whiskerRight
    (Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} Λ) (pullback.snd p i))
      (cbcClopenProjection Λ (StrictTower.squareLift k r p i h)))
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (pullback.fst p i)) ≫
  Functor.whiskerLeft
    (upperStar (ModuleCat.{u + 1} Λ) (pullback.snd p i) ⋙
      upperStar (ModuleCat.{u + 1} Λ) (StrictTower.squareLift k r p i h))
    ((proEtaleOpenExtensionComp Λ
        (StrictTower.squareLift k r p i h) (pullback.fst p i)).inv ≫
      (cbcOpenCongr Λ (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight
    ((upperStarComp (ModuleCat.{u + 1} Λ)
      (StrictTower.squareLift k r p i h) (pullback.snd p i)).inv ≫
      (cbcPullCongr Λ (pullback.lift_snd k r h)).hom)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)

attribute [local irreducible] upperStar Etale.upperStar comparisonUpperStar
  openImmersionLowerShriek Etale.openImmersionLowerShriek

/-- Comparison preserves the clopen projection with its outgoing compositors.
Source: Stacks Project, proetale.tex Tag 09AF and more-etale.tex Tag 0F7B;
steps 2--3 of lem-cbc-finite-clopen-alpha-site-transport
(blueprint: lem-cbc-finite-clopen-tail-site-transport).

Proof: write s for the clopen lift V → W ×_T S. On the image of s the
projection is the identity, and on its complementary open it is zero. The
sheaf axiom for this disjoint two-open cover uniquely specifies the map,
including when one component is empty. The comparison pullback preserves
restriction and the canonical open comparison preserves extension by zero;
thus these two component maps identify the etale and proetale projections.
Whisker this equality by pullback along q and extension by zero along b.
Use naturality of open comparison to move it through the projection. Its
composition equation for s and b combines the two extension functors, and
pullback comparison coherence for s and q combines inverse images.
Finally use equality transport along s;b=k and s;q=r. This is exactly the
stated equality of the two tails, with their source comparison displayed.
All assertions are on sheaves, before passing to complexes or localization. -/
theorem finiteClopenTailSiteTransport
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    let s := pullback.lift k r h
    letI := (Etale.ClopenMateNormalization.lift_clopen k r p i h).1
    letI := (Etale.ClopenMateNormalization.lift_clopen k r p i h).2
    let q := pullback.snd p i
    let b := pullback.fst p i
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) W).map
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b).map
            ((Etale.ClopenMateNormalization.projection Λ s).app
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) q).obj F)) ≫
          ((Etale.openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) s b).inv ≫
            (Etale.ClopenMateNormalization.openCongr Λ (pullback.lift_fst k r h)).hom).app
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) s).obj
                ((Etale.upperStar (ModuleCat.{u + 1} Λ) q).obj F)) ≫
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).map
            (((Etale.upperStarComp (ModuleCat.{u + 1} Λ) s q).inv ≫
              (eqToIso (congrArg (Etale.upperStar (ModuleCat.{u + 1} Λ))
                (pullback.lift_snd k r h))).hom).app F)) ≫
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) k).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) r).obj F) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).map
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) r).inv.app F) =
    (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ)
        (pullback.fst p i)).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.snd p i)).obj F) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (pullback.fst p i)).map
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ)
          (pullback.snd p i)).inv.app F) ≫
      (finiteClopenProEtaleTail Λ k i r p h).app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) S).obj F) := by
  let := (Etale.ClopenMateNormalization.lift_clopen k r p i h).1
  let := (Etale.ClopenMateNormalization.lift_clopen k r p i h).2
  exact tail_paste
    (A := comparisonUpperStar (ModuleCat.{u + 1} Λ) S)
    (B := comparisonUpperStar (ModuleCat.{u + 1} Λ) (pullback p i))
    (M := comparisonUpperStar (ModuleCat.{u + 1} Λ) V) (N := comparisonUpperStar (ModuleCat.{u + 1}
      Λ) W)
    (Q := Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.snd p i))
    (S := Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.lift k r h))
    (R := Etale.upperStar (ModuleCat.{u + 1} Λ) r)
    (J := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (pullback.lift k r h))
    (T := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (pullback.fst p i))
    (K := Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
    (Q' := upperStar (ModuleCat.{u + 1} Λ) (pullback.snd p i))
    (S' := upperStar (ModuleCat.{u + 1} Λ) (pullback.lift k r h)) (R' := upperStar (ModuleCat.{u +
      1} Λ) r)
    (J' := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (pullback.lift k r h))
    (T' := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (pullback.fst p i))
    (K' := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) (pullback.snd p i)).symm
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) (pullback.lift k r h)).symm
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) r).symm
    (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) (pullback.lift k r h))
    (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) (pullback.fst p i))
    (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) k)
    (Etale.ClopenMateNormalization.projection Λ (pullback.lift k r h))
    (cbcClopenProjection Λ (pullback.lift k r h))
    ((Etale.openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) (pullback.lift k r h)
        (pullback.fst p i)).inv ≫
      (Etale.ClopenMateNormalization.openCongr Λ (pullback.lift_fst k r h)).hom)
    ((proEtaleOpenExtensionComp Λ (pullback.lift k r h) (pullback.fst p i)).inv ≫
      (cbcOpenCongr Λ (pullback.lift_fst k r h)).hom)
    ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (pullback.lift k r h) (pullback.snd p i)).inv ≫
      (eqToIso (congrArg (Etale.upperStar (ModuleCat.{u + 1} Λ)) (pullback.lift_snd k r h))).hom)
    ((upperStarComp (ModuleCat.{u + 1} Λ) (pullback.lift k r h) (pullback.snd p i)).inv ≫
      (cbcPullCongr Λ (pullback.lift_snd k r h)).hom)
    (clopen_projection_comparison Λ (pullback.lift k r h))
    (open_compositor_comparison Λ (pullback.lift k r h) (pullback.fst p i) k
      (pullback.lift_fst k r h))
    (pull_compositor_comparison Λ (pullback.lift k r h) (pullback.snd p i) r
      (pullback.lift_snd k r h)) F

end AlgebraicGeometry.ProEtale
