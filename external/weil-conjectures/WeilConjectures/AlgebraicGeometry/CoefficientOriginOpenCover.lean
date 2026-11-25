/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Category.ULift
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful

/-! # Zariski locality of coefficient-sized etale origin

Source: Stacks Project, proetale.tex, Tag 09AK, proof of lemma-compare-constructible.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
open CategoryTheory.Functor.sheafPullbackConstruction

namespace AlgebraicGeometry.ProEtale

open Scheme

private theorem smallHomCompDown {C : Type u} [Category.{v} C]
    {T U V : AsSmall.{w} C} (g : T ⟶ U) (h : U ⟶ V) :
    ULift.down (g ≫ h) = ULift.down g ≫ ULift.down h := rfl

private theorem proCompLeft {X : Scheme.{u}} {T U V : X.ProEt}
    (g : T ⟶ U) (h : U ⟶ V) : (g ≫ h).left = g.left ≫ h.left := rfl

private theorem proSmallIdLeft {X : Scheme.{u}}
    (T : Scheme.coefficientProEtaleSiteModel.{u, v} X) :
    (ULift.down (𝟙 T : T ⟶ T)).left = 𝟙 (ULift.down T).left := rfl

private theorem toProEtObjHom {X : Scheme.{u}} (T : X.Etale) :
    (X.toProEt.obj T).hom = T.hom := rfl

private theorem toProEtObjLeft {X : Scheme.{u}} (T : X.Etale) :
    (X.toProEt.obj T).left = T.left := rfl

private theorem etMapObjHom {Y X : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    (T : Y.Etale) :
    ((MorphismProperty.Over.map ⊤ (inferInstance : Etale f)).obj T).hom = T.hom ≫ f := rfl

private theorem proMapObjHom {Y X : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    (T : Y.ProEt) :
    ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).obj T).hom =
      T.hom ≫ f := rfl

-- Override the successor-universe-only source instance locally in this section.
private instance (priority := 100000) largeModuleSheafify {C : Type*} [Category C]
    [EssentiallySmall.{w} C] (J : GrothendieckTopology C) (R : Type w) [CommRing R] :
    HasSheafify J (ModuleCat.{w} R) := by
  let e := equivSmallModel.{w} C
  have : HasSheafify (e.inverse.inducedTopology J) (ModuleCat.{w} R) :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  exact e.hasSheafify J (e.inverse.inducedTopology J) _

section OriginalComparison
open Scheme
variable (S : Scheme.{u}) (R : Type (max v (u + 1))) [CommRing R]

private theorem additivePreservesRelative (F : S.Etaleᵒᵖ ⥤ (ModuleCat.{max v (u + 1)} R)) :
    Functor.PreservesRelativeFilteredColimits.{u} (AffineEtale.toAffineProEt S)
      ((AffineProEt.toProEt S).op ⋙ (Scheme.toProEt S).op.lan.obj F) := by
  constructor
  intro I _ _ K c hc
  -- The limit cone in the pro-étale site.
  have hc₁ : IsLimit ((AffineProEt.toProEt S).mapCone c) := isLimitOfPreserves _ hc
  -- The limit cone in `Over S`, obtained by reflecting the `Scheme`-level limit cone
  -- along `Over.forget S`.
  have hcOver : IsLimit ((ProEt.forget S).mapCone ((AffineProEt.toProEt S).mapCone c)) :=
    isLimitOfReflects (CategoryTheory.Over.forget S)
      (((AffineProEt.isLimitMapConeToSchemeOfIsLimit c hc).ofIsoLimit
        (Functor.mapConeMapCone c).symm).ofIsoLimit (Functor.mapConeMapCone _).symm)
  -- The comparison of the two relevant diagrams in the pro-étale site.
  have e : (K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S ≅
      (K ⋙ AffineEtale.Spec S) ⋙ Scheme.toProEt S :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft K (AffineEtale.toAffineProEtCompToProEtIso S) ≪≫
      (Functor.associator _ _ _).symm
  -- Mapping into an étale `S`-scheme commutes with the cofiltered limit, by
  -- `Scheme.preservesColimit_yoneda`.
  have hpres : ∀ (X : S.Etaleᵒᵖ),
      PreservesColimit ((K ⋙ AffineEtale.Spec S).op ⋙ (Scheme.toProEt S).op)
        (coyoneda.obj (Opposite.op ((Scheme.toProEt S).op.obj X))) := by
    intro X
    have h₁ : ∀ {i j : I} (f : i ⟶ j), IsAffineHom
        ((((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S) ⋙
          ProEt.forget S).map f).left :=
      fun f ↦ inferInstanceAs
        (IsAffineHom ((AffineEtale.toAffineProEt S).map (K.map f)).left)
    have h₂ : ∀ (i : I), CompactSpace
        ((((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S) ⋙
          ProEt.forget S).obj i).left :=
      fun i ↦ inferInstanceAs (CompactSpace ((AffineEtale.toAffineProEt S).obj (K.obj i)).left)
    have h₃ : ∀ (i : I), QuasiSeparatedSpace
        ((((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S) ⋙
          ProEt.forget S).obj i).left :=
      fun i ↦ inferInstanceAs
        (QuasiSeparatedSpace ((AffineEtale.toAffineProEt S).obj (K.obj i)).left)
    have h₄ : LocallyOfFinitePresentation
        ((ProEt.forget S).obj ((Scheme.toProEt S).obj X.unop)).hom :=
      inferInstanceAs (LocallyOfFinitePresentation X.unop.hom)
    have := Scheme.preservesColimit_yoneda
      (((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S) ⋙ ProEt.forget S)
      ((ProEt.forget S).obj ((Scheme.toProEt S).obj X.unop))
    have hyon : IsColimit
        ((yoneda.obj ((ProEt.forget S).obj ((Scheme.toProEt S).obj X.unop))).mapCocone
          ((ProEt.forget S).mapCone ((AffineProEt.toProEt S).mapCone c)).op) :=
      isColimitOfPreserves _ hcOver.op
    have hy : IsColimit ((yoneda.obj ((Scheme.toProEt S).obj X.unop)).mapCocone
        ((AffineProEt.toProEt S).mapCone c).op) :=
      IsColimit.mapCoconeEquiv (ProEt.forgetOpCompYonedaIso ((Scheme.toProEt S).obj X.unop))
        (by exact hyon)
    have hco : IsColimit ((coyoneda.obj (Opposite.op ((Scheme.toProEt S).op.obj X))).mapCocone
        ((AffineProEt.toProEt S).mapCone c).op) :=
      IsColimit.mapCoconeEquiv (Coyoneda.objOpOp _).symm hy
    let : PreservesColimit ((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S).op
        (coyoneda.obj (Opposite.op ((Scheme.toProEt S).op.obj X))) :=
      preservesColimit_of_preserves_colimit_cocone hc₁.op hco
    exact preservesColimit_of_iso_diagram _ (NatIso.op e).symm
  let : PreservesColimit ((K ⋙ AffineEtale.Spec S).op ⋙ (Scheme.toProEt S).op)
      ((Scheme.toProEt S).op.leftKanExtension F) := inferInstance
  have e' : (K ⋙ AffineEtale.Spec S).op ⋙ (Scheme.toProEt S).op ≅
      ((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S).op := NatIso.op e
  let : PreservesColimit ((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S).op
      ((Scheme.toProEt S).op.leftKanExtension F) :=
    preservesColimit_of_iso_diagram _ e'
  exact ⟨isColimitOfPreserves ((Scheme.toProEt S).op.leftKanExtension F) hc₁.op⟩

private theorem additiveIsSheaf (F : S.Etaleᵒᵖ ⥤ (ModuleCat.{max v (u + 1)} R))
    (hF : Presheaf.IsSheaf (smallEtaleTopology S) F) :
    Presheaf.IsSheaf (AffineProEt.topology S)
      ((AffineProEt.toProEt S).op ⋙ (Scheme.toProEt S).op.lan.obj F) := by
  let _ := additivePreservesRelative S R F
  let _ : HasFilteredColimitsOfSize.{u, u} (ModuleCat.{max v (u + 1)} R) :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, max v (u + 1), max v (u + 1)}
  let _ : AB5OfSize.{u, u} (ModuleCat.{max v (u + 1)} R) :=
    AB5OfSize_of_univLE.{u, u, max v (u + 1), max v (u + 1)} _
  apply Presheaf.isSheaf_of_generates_of_isRelativelyPresentable
      (AffineEtale.toAffineProEt S) (AffineProEt.minimalPrecoverage S)
      (AffineEtale.topology S)
  · let iso : (AffineEtale.toAffineProEt S).op ⋙
        (AffineProEt.toProEt S).op ⋙ S.toProEt.op.lan.obj F ≅
        (AffineEtale.Spec S).op ⋙ F :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Functor.opComp _ _).symm _ ≪≫
        Functor.isoWhiskerRight
          (NatIso.op (AffineEtale.toAffineProEtCompToProEtIso S).symm) _ ≪≫
        Functor.isoWhiskerRight (Functor.opComp _ _) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (asIso <| ((Scheme.toProEt S).op.lanUnit.app F)).symm
    rw [Presheaf.isSheaf_of_iso_iff iso]
    exact Functor.op_comp_isSheaf_of_isSheaf _ _ _ _ hF
  · exact AffineProEt.generates_minimalPrecoverage S
  · exact AffineProEt.minimalPrecoverage_le_relativelyPresentable S
  · exact AffineProEt.minimalPrecoverage_le_finite S

private theorem additiveUnitIso :
    IsIso (sheafAdjunctionContinuous (toProEt S) (ModuleCat.{max v (u + 1)} R)
      S.smallEtaleTopology (ProEt.topology S)).unit := by
  let A := (ModuleCat.{max v (u + 1)} R)
  let adj := sheafAdjunctionContinuous (toProEt S) A S.smallEtaleTopology (ProEt.topology S)
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  let G := (AffineEtale.Spec S).sheafPushforwardContinuous A (AffineEtale.topology S)
    S.smallEtaleTopology
  suffices IsIso ((G ⋙ sheafToPresheaf _ A).map (adj.unit.app F)) from
    isIso_of_reflects_iso _ (G ⋙ sheafToPresheaf _ A)
  change IsIso ((AffineEtale.Spec S).op.whiskerLeft (adj.unit.app F).hom)
  have hu : (adj.unit.app F).hom =
      (toProEt S).op.lanUnit.app F.obj ≫
        (toProEt S).op.whiskerLeft (toSheafify _ ((toProEt S).op.lan.obj F.obj)) := by
    change (sheafToPresheaf _ A).map (adj.unit.app F) = _
    dsimp only [adj]
    rw [sheafAdjunctionContinuous, Adjunction.map_restrictFullyFaithful_unit_app]
    simp
    rfl
  rw [hu, Functor.whiskerLeft_comp]
  have : HasLimitsOfSize.{u, u + 1} A :=
    hasLimitsOfSizeShrink.{u, u + 1, max v (u + 1), max v (u + 1)} A
  have h2 : IsIso ((AffineProEt.toProEt S).op.whiskerLeft
      (toSheafify (ProEt.topology S) ((toProEt S).op.lan.obj F.obj))) :=
    Functor.IsDenseSubsite.isIso_whiskerLeft_toSheafify (AffineProEt.topology S) _ _ A _
      (additiveIsSheaf S R F.obj F.property)
  have h3 : IsIso ((AffineEtale.Spec S).op.whiskerLeft ((toProEt S).op.whiskerLeft
      (toSheafify (ProEt.topology S) ((toProEt S).op.lan.obj F.obj)))) := by
    rw [NatTrans.isIso_iff_isIso_app] at h2 ⊢
    intro U
    exact h2 (Opposite.op ((AffineEtale.toAffineProEt S).obj U.unop))
  infer_instance

end OriginalComparison

private def smallModelModuleFullyFaithful (X : Scheme.{u})
    (R : Type (max v (u + 1))) [CommRing R] :
    (sheafPullback (Scheme.smallModelComparisonInclusion.{u, v} X)
      (ModuleCat.{max v (u + 1)} R) (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).FullyFaithful := by
  let A := (ModuleCat.{max v (u + 1)} R)
  let J := Scheme.smallModelComparisonEtaleTopology.{u, v} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  have : (AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).isEquivalence_inverse
  have : (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).isEquivalence_inverse
  have : (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).inverse.IsDenseSubsite
      J X.smallEtaleTopology := by
    change (AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsDenseSubsite
      ((AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).inducedTopology
        X.smallEtaleTopology) X.smallEtaleTopology
    infer_instance
  have : (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).inverse.IsDenseSubsite
      K (ProEt.topology X) := by
    change (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).IsDenseSubsite
      ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).inducedTopology
        (ProEt.topology X)) (ProEt.topology X)
    infer_instance
  let eE : Sheaf X.smallEtaleTopology A ≌ Sheaf J A :=
    Equivalence.sheafCongr X.smallEtaleTopology J
      (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)) A
  let eP : Sheaf (Scheme.ProEt.topology X) A ≌ Sheaf K A :=
    Equivalence.sheafCongr (Scheme.ProEt.topology X) K
      (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)) A
  let L := sheafPullback (Scheme.toProEt X) A X.smallEtaleTopology (ProEt.topology X)
  let adjL := sheafAdjunctionContinuous (Scheme.toProEt X) A
    X.smallEtaleTopology (ProEt.topology X)
  have : IsIso adjL.unit := additiveUnitIso.{u, v} X R
  have : L.Faithful := adjL.faithful_L_of_mono_unit_app
  have : L.Full := adjL.full_L_of_isSplitEpi_unit_app
  let adj := eE.symm.toAdjunction.comp (adjL.comp eP.toAdjunction)
  let F := Scheme.smallModelComparisonInclusion.{u, v} X
  let R := (Scheme.toProEt X).sheafPushforwardContinuous A
    X.smallEtaleTopology (ProEt.topology X)
  let qR : (eP.inverse ⋙ R) ⋙ eE.functor ≅ F.sheafPushforwardContinuous A J K :=
    NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ (Iso.refl _))
      (by intro M N f; ext U; rfl)
  have ha : (eE.inverse ⋙ L ⋙ eP.functor) ⊣
      F.sheafPushforwardContinuous A J K := by
    exact adj.ofNatIsoRight qR
  let q := ha.leftAdjointUniq (sheafAdjunctionContinuous F A J K)
  have : (sheafPullback F A J K).Faithful := Functor.Faithful.of_iso q
  have : (sheafPullback F A J K).Full := Functor.Full.of_iso q
  exact Functor.FullyFaithful.ofFullyFaithful _

private def proLoc {Y X : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f] :
    Scheme.coefficientProEtaleSiteModel.{u, v} Y ⥤
      Scheme.coefficientProEtaleSiteModel.{u, v} X :=
  AsSmall.down ⋙ MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f) ⋙ AsSmall.up

private def etLoc {Y X : Scheme.{u}} (f : Y ⟶ X) [Etale f] :
    Scheme.smallModelComparisonEtaleSite.{u, v} Y ⥤
      Scheme.smallModelComparisonEtaleSite.{u, v} X :=
  AsSmall.down ⋙ MorphismProperty.Over.map ⊤ (inferInstance : Etale f) ⋙ AsSmall.up

private instance proLocContinuous {Y X : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f] :
    (proLoc.{u, v} f).IsContinuous
      (Scheme.coefficientProEtaleModelTopology.{u, v} Y)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) := by
  have : (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).IsContinuous
      (Scheme.ProEt.topology X) (Scheme.coefficientProEtaleModelTopology.{u, v} X) :=
    Scheme.coefficientProEtaleModelUp_isContinuous.{u, v} X
  have := Functor.isContinuous_comp
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f))
    (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X)
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)
  exact Functor.isContinuous_comp AsSmall.down
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f) ⋙ AsSmall.up)
    (Scheme.coefficientProEtaleModelTopology.{u, v} Y) (Scheme.ProEt.topology Y)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)

private instance etLocContinuous {Y X : Scheme.{u}} (f : Y ⟶ X) [Etale f] :
    (etLoc.{u, v} f).IsContinuous
      (Scheme.smallModelComparisonEtaleTopology.{u, v} Y)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) := by
  have : (AsSmall.up : X.Etale ⥤ Scheme.smallModelComparisonEtaleSite.{u, v} X).IsContinuous
      X.smallEtaleTopology (Scheme.smallModelComparisonEtaleTopology.{u, v} X) :=
    inferInstanceAs
      ((AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).functor.IsContinuous
        X.smallEtaleTopology
        ((AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).inverse.inducedTopology
          X.smallEtaleTopology))
  have : (MorphismProperty.Over.map ⊤ (inferInstance : Etale f)).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology :=
    Scheme.isContinuous_overMap (inferInstance : Etale f) le_rfl
  have := Functor.isContinuous_comp
    (MorphismProperty.Over.map ⊤ (inferInstance : Etale f))
    (AsSmall.up : X.Etale ⥤ Scheme.smallModelComparisonEtaleSite.{u, v} X)
    Y.smallEtaleTopology X.smallEtaleTopology
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
  exact Functor.isContinuous_comp AsSmall.down
    (MorphismProperty.Over.map ⊤ (inferInstance : Etale f) ⋙ AsSmall.up)
    (Scheme.smallModelComparisonEtaleTopology.{u, v} Y) Y.smallEtaleTopology
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X)

private def proLocAdj {Y X : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f] :
    proLoc.{u, v} f ⊣ Scheme.coefficientProEtaleModelBaseChange.{u, v} f :=
  (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := Y.ProEt)).symm.toAdjunction.comp
    ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f inferInstance trivial).comp
      (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).toAdjunction)

private def etLocAdj {Y X : Scheme.{u}} (f : Y ⟶ X) [Etale f] :
    etLoc.{u, v} f ⊣ Scheme.coefficientEtaleBaseChange.{u, v} f :=
  (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := Y.Etale)).symm.toAdjunction.comp
    ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ f inferInstance trivial).comp
      (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).toAdjunction)

private abbrev comparisonLeft (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :=
  sheafPullback (Scheme.smallModelComparisonInclusion.{u, v} X)
    (ModuleCat.{max v (u + 1)} A) (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)

private abbrev comparisonRight (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :=
  (Scheme.smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous
    (ModuleCat.{max v (u + 1)} A) (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)

private abbrev comparisonAdj (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :=
  sheafAdjunctionContinuous (Scheme.smallModelComparisonInclusion.{u, v} X)
    (ModuleCat.{max v (u + 1)} A) (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)

private abbrev proRestriction {Y X : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    (A : Type (max v (u + 1))) [CommRing A] :=
  (proLoc.{u, v} f).sheafPushforwardContinuous (ModuleCat.{max v (u + 1)} A)
    (Scheme.coefficientProEtaleModelTopology.{u, v} Y)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)

private abbrev etRestriction {Y X : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    (A : Type (max v (u + 1))) [CommRing A] :=
  (etLoc.{u, v} f).sheafPushforwardContinuous (ModuleCat.{max v (u + 1)} A)
    (Scheme.smallModelComparisonEtaleTopology.{u, v} Y)
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X)

private def comparisonRestrictionIso {Y X : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    (A : Type (max v (u + 1))) [CommRing A] :
    (comparisonRight.{u, v} X A) ⋙ etRestriction.{u, v} f A ≅
      proRestriction.{u, v} f A ⋙ (comparisonRight.{u, v} Y A) :=
  NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _ (Iso.refl _))
    (by intro F G g; ext V; rfl)

private theorem comparisonRestrictionMate_isIso {Y X : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    (A : Type (max v (u + 1))) [CommRing A] :
    IsIso ((mateEquiv (comparisonAdj.{u, v} X A) (comparisonAdj.{u, v} Y A)).symm
      (comparisonRestrictionIso.{u, v} f A).hom) := by
  let p := (proLocAdj.{u, v} f).sheafPushforwardContinuous
    (E := ModuleCat.{max v (u + 1)} A)
    (Scheme.coefficientProEtaleModelTopology.{u, v} Y)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)
  let e := (etLocAdj.{u, v} f).sheafPushforwardContinuous
    (E := ModuleCat.{max v (u + 1)} A)
    (Scheme.smallModelComparisonEtaleTopology.{u, v} Y)
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
  let q := (comparisonRestrictionIso.{u, v} f A).hom
  have h : IsIso ((mateEquiv p e) q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro F
    rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
    intro V
    have heq : (((mateEquiv p e) q).app F).hom.app V = 𝟙 _ := by
      let c := (etLocAdj.{u, v} f).counit.app V.unop
      let n := (proLocAdj.{u, v} f).unit.app
        ((Scheme.smallModelComparisonInclusion.{u, v} Y).obj
          ((Scheme.coefficientEtaleBaseChange.{u, v} f).obj V.unop))
      let t := (Scheme.coefficientProEtaleModelBaseChange.{u, v} f).map
        ((Scheme.smallModelComparisonInclusion.{u, v} X).map c)
      let H := (Functor.sheafPushforwardContinuous
        (Scheme.coefficientProEtaleModelBaseChange.{u, v} f) (ModuleCat.{max v (u + 1)} A)
          (Scheme.coefficientProEtaleModelTopology.{u, v} X)
          (Scheme.coefficientProEtaleModelTopology.{u, v} Y)).obj F
      let W := (Scheme.coefficientEtaleBaseChange.{u, v} f).obj V.unop
      let M := ((etRestriction.{u, v} f A).obj
        ((comparisonRight.{u, v} X A).obj H)).obj.obj (op W)
      let N := ((proRestriction.{u, v} f A).obj H).obj.obj
        (op ((Scheme.smallModelComparisonInclusion.{u, v} Y).obj W))
      have hs : F.obj.map t.op ≫ 𝟙 M ≫ 𝟙 N ≫ F.obj.map n.op = 𝟙 _ := by
        erw [Category.id_comp, Category.id_comp]
        rw [← F.obj.map_comp, ← F.obj.map_id]
        congr 1
        apply Quiver.Hom.unop_inj
        simp only [unop_comp, Quiver.Hom.unop_op, unop_id]
        apply ULift.ext
        apply MorphismProperty.Over.Hom.ext
        apply pullback.hom_ext <;>
          simp only [Functor.comp_obj, MorphismProperty.Over.pullback, Functor.id_obj,
            Functor.const_obj_obj, MorphismProperty.Over.mk, MorphismProperty.Over.homMk,
            AsSmall.up, AsSmall.down, toProEtObjLeft, toProEtObjHom, proEtaleBaseChange,
            etLoc, etMapObjHom f, proLocAdj, Adjunction.comp, AsSmall.equiv, eqToIso_refl,
            Equivalence.symm_functor, Equivalence.symm_inverse, Equivalence.toAdjunction,
            Equivalence.Equivalence_mk'_unit, Equivalence.Equivalence_mk'_counit,
            MorphismProperty.Over.mapPullbackAdj, proMapObjHom f, Functor.whiskerRight_comp,
            Category.assoc, Equivalence.symm_unit, Equivalence.Equivalence_mk'_counitInv,
            Equivalence.symm_counit, Equivalence.Equivalence_mk'_unitInv, Adjunction.mk'_unit,
            Functor.whiskerLeft_comp, Adjunction.mk'_counit, NatTrans.comp_app,
            NatIso.ofComponents_inv_app, Iso.refl_inv, Functor.whiskerRight_app,
            Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, MorphismProperty.Comma.id_hom,
            Comma.id_left, Category.comp_id, pullback.lift_fst_snd, NatIso.ofComponents_hom_app,
            Iso.refl_hom, Functor.associator_inv_app, Functor.associator_hom_app,
            Category.id_comp, Functor.comp_map, etLocAdj, CategoryTheory.Functor.map_id,
            Functor.rightUnitor_hom_app, Functor.map_comp, smallHomCompDown (C := X.Etale),
            toProEt_map_hom, Over.homMk_left, smallHomCompDown (C := Y.ProEt), proCompLeft,
            limit.lift_π, PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_left,
            proSmallIdLeft.{u, v} (X := Y), n, t, c]
        all_goals exact Category.id_comp _
      simpa [mateEquiv, p, e, q, comparisonRestrictionIso,
        Adjunction.sheafPushforwardContinuous, c, n, t, H, W, M, N,
        etRestriction, proRestriction, comparisonRight,
        Functor.sheafPushforwardContinuous] using hs
    rw [heq]
    infer_instance
  let b := (mateEquiv (comparisonAdj.{u, v} X A) (comparisonAdj.{u, v} Y A)).symm q
  have hi := iterated_mateEquiv_conjugateEquiv
    (comparisonAdj.{u, v} X A) (comparisonAdj.{u, v} Y A) e p b
  rw [Equiv.apply_symm_apply] at hi
  have : IsIso (conjugateEquiv ((comparisonAdj.{u, v} X A).comp p)
      (e.comp (comparisonAdj.{u, v} Y A)) b) := by
    rw [← hi]
    exact h
  change IsIso b
  exact conjugateEquiv_of_iso ((comparisonAdj.{u, v} X A).comp p)
    (e.comp (comparisonAdj.{u, v} Y A)) b

private def proPullbackRestrictionIso {Y X : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    (A : Type (max v (u + 1))) [CommRing A] :
    Scheme.coefficientProEtaleFixedModulePullback.{u, v} f A ≅ proRestriction.{u, v} f A :=
  (sheafAdjunctionContinuous (Scheme.coefficientProEtaleModelBaseChange.{u, v} f)
    (ModuleCat.{max v (u + 1)} A) (Scheme.coefficientProEtaleModelTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} Y)).leftAdjointUniq
      ((proLocAdj.{u, v} f).sheafPushforwardContinuous
        (E := ModuleCat.{max v (u + 1)} A)
        (Scheme.coefficientProEtaleModelTopology.{u, v} Y)
        (Scheme.coefficientProEtaleModelTopology.{u, v} X))

private theorem restrictedCounit_isIso {Y X : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    (A : Type (max v (u + 1))) [CommRing A]
    (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A))
    (hF : (comparisonLeft.{u, v} Y A).essImage
      ((proRestriction.{u, v} f A).obj F)) :
    IsIso ((proRestriction.{u, v} f A).map ((comparisonAdj.{u, v} X A).counit.app F)) := by
  let ff := smallModelModuleFullyFaithful.{u, v} Y A
  have : (comparisonLeft.{u, v} Y A).Full := ff.full
  have : (comparisonLeft.{u, v} Y A).Faithful := ff.faithful
  have : IsIso ((comparisonAdj.{u, v} Y A).counit.app
      ((proRestriction.{u, v} f A).obj F)) :=
    ((comparisonAdj.{u, v} Y A).isIso_counit_app_iff_mem_essImage).mpr hF
  let q := (comparisonRestrictionIso.{u, v} f A).hom
  let b := (mateEquiv (comparisonAdj.{u, v} X A) (comparisonAdj.{u, v} Y A)).symm q
  have : IsIso b := comparisonRestrictionMate_isIso.{u, v} f A
  have hb := mateEquiv_counit_symm (comparisonAdj.{u, v} X A)
    (comparisonAdj.{u, v} Y A) q F
  have : IsIso (b.app ((comparisonRight.{u, v} X A).obj F) ≫
      (proRestriction.{u, v} f A).map ((comparisonAdj.{u, v} X A).counit.app F)) := by
    rw [← hb]
    infer_instance
  exact IsIso.of_isIso_comp_left (b.app _) _

private theorem isIso_of_openRestrictions (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] {I : Type u}
    (U : I → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    {F G : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A)} (φ : F ⟶ G)
    (hφ : ∀ i, IsIso ((proRestriction.{u, v} (U i).ι A).map φ)) : IsIso φ := by
  let V : I → X.ProEt := fun i ↦ Scheme.ProEt.mk (U i).ι
  have hcover : (Scheme.ProEt.topology X).CoversTop V := by
    intro T
    let O (i : I) := T.hom ⁻¹ᵁ U i
    apply Scheme.ProEt.mem_topology_of_openImmersion _ (fun i ↦ (O i).ι)
    · intro x
      obtain ⟨i, hi⟩ := hU (T.hom x)
      exact ⟨i, ⟨⟨x, hi⟩, rfl⟩⟩
    · intro i
      refine ⟨i, ⟨?_⟩⟩
      exact MorphismProperty.Over.homMk (T.hom.resLE (U i) (O i) le_rfl)
        (T.hom.resLE_comp_ι le_rfl)
  let P := Functor.sheafPushforwardContinuous
    (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X)
      (ModuleCat.{max v (u + 1)} A)
      (Scheme.ProEt.topology X) (Scheme.coefficientProEtaleModelTopology.{u, v} X)
  have hP : IsIso (P.map φ) := by
    apply Sheaf.isIso_of_coversTop hcover
    intro i
    have := hφ i
    rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
    intro Z
    let W : (U i).toScheme.ProEt := Scheme.ProEt.mk Z.unop.hom.left
    let e : (MorphismProperty.Over.map ⊤
        (inferInstance : WeaklyEtale (U i).ι)).obj W ≅ Z.unop.left :=
      MorphismProperty.Over.isoMk (Iso.refl _)
        (by
          change 𝟙 _ ≫ Z.unop.left.hom = Z.unop.hom.left ≫ (U i).ι
          rw [Category.id_comp]
          exact (MorphismProperty.Over.w Z.unop.hom).symm)
    have hW := (NatTrans.isIso_iff_isIso_app
      ((proRestriction.{u, v} (U i).ι A).map φ).hom).mp
        (inferInstanceAs (IsIso ((proRestriction.{u, v} (U i).ι A).map φ).hom))
          (op (AsSmall.up.obj W))
    exact (NatTrans.isIso_app_iff_of_iso φ.hom
      (Functor.mapIso
        (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X) e).op).mpr hW
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro Z
  exact (NatTrans.isIso_iff_isIso_app (P.map φ).hom).mp
    (inferInstanceAs (IsIso (P.map φ).hom)) (op (ULift.down Z.unop))

/-- Etale origin is local for an open cover, with coefficients of independent size.
Source: Stacks Project, Tag 09AK, proof of lemma-compare-constructible, the sentence
"Since it suffices to prove this locally on X"; Tags 099T and 099Y, comparison
full faithfulness and compatibility with restriction
(auxiliary; not a blueprint node).

Proof: let L be comparison inverse image, R its direct image, and epsilon the counit.
Restriction along an open immersion commutes with L and R: both right adjoints are
precomposition along the corresponding base-change functors, and localization at
an open is restriction to the associated slice site. The adjunction mate identifies
the restricted epsilon with the comparison counit of the restricted sheaf.
On each covering open the sheaf is in the image of L, so its counit is invertible
by full faithfulness of L. Invertibility of a sheaf morphism is local for a covering
family; hence epsilon is invertible globally. Its source L(R(F)) supplies the etale
antecedent. For an empty base the empty cover gives the same argument, since every
sheaf morphism there is invertible. All constructions use the coefficient-sized
small models: their site equivalences preserve covers, the sectionwise direct
images, and the adjunction mates. The proof is valid for arbitrary modules and
does not use finite generation, a Noetherian ring, or quasi-compactness. -/
theorem coefficientFixed_essImage_of_openCover (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] {I : Type u}
    (U : I → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A))
    (hF : ∀ i, (Functor.sheafPullbackConstruction.sheafPullback
      (Scheme.smallModelComparisonInclusion.{u, v} (U i).toScheme) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} (U i).toScheme)
      (Scheme.coefficientProEtaleModelTopology.{u, v} (U i).toScheme)).essImage
      ((Scheme.coefficientProEtaleFixedModulePullback.{u, v} (U i).ι A).obj F)) :
    (Functor.sheafPullbackConstruction.sheafPullback
      (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).essImage F := by
  have hlocal (i : I) : (comparisonLeft.{u, v} (U i).toScheme A).essImage
      ((proRestriction.{u, v} (U i).ι A).obj F) := by
    obtain ⟨G, ⟨e⟩⟩ := hF i
    exact ⟨G, ⟨e ≪≫ (proPullbackRestrictionIso.{u, v} (U i).ι A).app F⟩⟩
  have : IsIso ((comparisonAdj.{u, v} X A).counit.app F) :=
    isIso_of_openRestrictions.{u, v} X A U hU _
      (fun i ↦ restrictedCounit_isIso.{u, v} (U i).ι A F (hlocal i))
  exact ⟨(comparisonRight.{u, v} X A).obj F,
    ⟨asIso ((comparisonAdj.{u, v} X A).counit.app F)⟩⟩

end AlgebraicGeometry.ProEtale
