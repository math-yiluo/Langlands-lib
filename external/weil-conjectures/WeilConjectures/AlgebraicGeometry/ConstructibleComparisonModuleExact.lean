/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Exactness and faithfulness on intrinsic comparison modules
Source: Stacks Project, Tags 00YV and 099T.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace AlgebraicGeometry.ProEtale
open Scheme

section ConstantPresentation
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K]
  {W : C} (hW : IsTerminal W) (hFW : IsTerminal (F.obj W))
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private def constantPullbackIso (A : Type u) :
    (constantSheaf K (Type u)).obj A ≅
      (sheafPullback F (Type u) J K).obj ((constantSheaf J (Type u)).obj A) :=
  ((conjugateIsoEquiv
    ((constantSheafAdj J (Type u) hW).comp
      (sheafAdjunctionContinuous F (Type u) J K))
    (constantSheafAdj K (Type u) hFW)).symm
      (F.sheafPushforwardContinuousCompSheafSectionsObjIso (Type u) J K (op W))).app A
private theorem constantPullback_unit (A : Type u) :
    ((sheafificationAdjunction K (Type u)).unit.app ((Functor.const Dᵒᵖ).obj A)).app
        (op (F.obj W)) ≫
      (constantPullbackIso F J K hW hFW A).hom.hom.app (op (F.obj W)) =
    ((sheafificationAdjunction J (Type u)).unit.app ((Functor.const Cᵒᵖ).obj A)).app (op W) ≫
      ((sheafAdjunctionContinuous F (Type u) J K).unit.app
        ((constantSheaf J (Type u)).obj A)).hom.app (op W) := by
  have h := unit_conjugateEquiv_symm
    ((constantSheafAdj J (Type u) hW).comp
      (sheafAdjunctionContinuous F (Type u) J K))
    (constantSheafAdj K (Type u) hFW)
    (F.sheafPushforwardContinuousCompSheafSectionsObjIso (Type u) J K (op W)).hom A
  simpa [constantPullbackIso, constantSheafAdj, Adjunction.comp_unit_app,
    Functor.sheafPushforwardContinuousCompSheafSectionsObjIso] using h.symm

private theorem constantPullback_unit_all (A : Type u) (U : Cᵒᵖ) :
    (toSheafify K ((Functor.const Dᵒᵖ).obj A)).app (F.op.obj U) ≫
      (constantPullbackIso F J K hW hFW A).hom.hom.app (F.op.obj U) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U ≫
      ((sheafAdjunctionContinuous F (Type u) J K).unit.app
        ((constantSheaf J (Type u)).obj A)).hom.app U := by
  let a := (toSheafify K ((Functor.const Dᵒᵖ).obj A)) ≫
    (constantPullbackIso F J K hW hFW A).hom.hom
  let b := toSheafify J ((Functor.const Cᵒᵖ).obj A) ≫
    ((sheafAdjunctionContinuous F (Type u) J K).unit.app
      ((constantSheaf J (Type u)).obj A)).hom
  have ha := a.naturality (F.op.map (hW.from U.unop).op)
  have hb := b.naturality (hW.from U.unop).op
  change a.app (F.op.obj U) = a.app (op (F.obj W)) ≫ _ at ha
  change b.app U = b.app (op W) ≫ _ at hb
  have ht := constantPullback_unit F J K hW hFW A
  change a.app (op (F.obj W)) = b.app (op W) at ht
  simpa only [a, b, NatTrans.comp_app] using
    ha.trans ((congrArg (fun z ↦ z ≫ _) ht).trans hb.symm)

private theorem constantForget_unit (J : GrothendieckTopology C)
    (A : Type u) [CommRing A] :
    Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
        (forget CommRingCat.{u}) ≫
      ((constantCommuteCompose J (forget CommRingCat.{u})).app (CommRingCat.of A)).hom.hom =
        toSheafify J ((Functor.const Cᵒᵖ).obj A) := by
  change Functor.whiskerRight
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
    (forget CommRingCat.{u}) ≫
      ((constantCommuteCompose J (forget CommRingCat.{u})).hom.app
        (CommRingCat.of A)).hom = _
  rw [constantCommuteCompose_hom_app_hom, ← Category.assoc,
    sheafComposeIso_inv_fac]
  rw [← toSheafify_naturality]
  rfl

private def canonicalRingMap (A : Type u) [CommRing A] :
    (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A) ⟶
      (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj
        ((constantSheaf K CommRingCat.{u}).obj (CommRingCat.of A)) :=
  ((sheafificationAdjunction J CommRingCat.{u}).homEquiv _ _).symm
    (Functor.whiskerLeft F.op (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of A))))

include hW hFW in
private theorem ringPresentation (A : Type u) [CommRing A] :
    ∃ pr : SheafPullbackUnitPresentation (F := F)
      ((sheafCompose J (forget CommRingCat.{u})).obj
        ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
      ((sheafCompose K (forget CommRingCat.{u})).obj
        ((constantSheaf K CommRingCat.{u}).obj (CommRingCat.of A))),
      pr.unit = (sheafCompose J (forget CommRingCat.{u})).map
        (canonicalRingMap F J K A) := by
  let R := (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)
  let S := (constantSheaf K CommRingCat.{u}).obj (CommRingCat.of A)
  let UJ := sheafCompose J (forget CommRingCat.{u})
  let UK := sheafCompose K (forget CommRingCat.{u})
  let eJ := (constantCommuteCompose J (forget CommRingCat.{u})).app (CommRingCat.of A)
  let eK := (constantCommuteCompose K (forget CommRingCat.{u})).app (CommRingCat.of A)
  let L := sheafPullback F (Type u) J K
  let adj := sheafAdjunctionContinuous F (Type u) J K
  let φ := canonicalRingMap F J K A
  let e : UK.obj S ≅ L.obj (UJ.obj R) :=
    eK ≪≫ constantPullbackIso F J K hW hFW A ≪≫ L.mapIso eJ.symm
  let φs : UJ.obj R ⟶ (F.sheafPushforwardContinuous (Type u) J K).obj (UK.obj S) :=
    UJ.map φ
  refine ⟨⟨φs, e, ?_⟩, rfl⟩
  have hφ : toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)) ≫ φ.hom =
      Functor.whiskerLeft F.op (toSheafify K
        ((Functor.const Dᵒᵖ).obj (CommRingCat.of A))) := by
    exact ((sheafificationAdjunction J CommRingCat.{u}).homEquiv _ _).apply_symm_apply _
  have he : φs ≫ (F.sheafPushforwardContinuous (Type u) J K).map e.hom =
      adj.unit.app (UJ.obj R) := by
    apply (cancel_epi eJ.inv).mp
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ ((F.sheafPushforwardContinuous (Type u) J K).obj
      (L.obj (UJ.obj R))).property
    ext U a
    have hj := congrArg (fun t ↦ t.app U a) (constantForget_unit J A)
    have hk := congrArg (fun t ↦ t.app (F.op.obj U) a) (constantForget_unit K A)
    have hp := congrArg (fun t ↦ t.app U a) hφ
    have hc := congrArg (fun t ↦ t a)
      (constantPullback_unit_all F J K hW hFW A U)
    have hn := congrArg (fun t ↦ t.hom.app U)
      (adj.unit.naturality eJ.inv)
    dsimp only [NatTrans.comp_app] at hj hk hp hc
    have hiJ : eJ.inv.hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a) =
          (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a := by
      have hj' : eJ.hom.hom.app U
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a) =
            (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a := hj
      exact (congrArg (fun x ↦ eJ.inv.hom.app U x) hj').symm.trans
        (ConcreteCategory.congr_hom
          (congrArg (fun t ↦ t.hom.app U) eJ.hom_inv_id) _)
    change (L.map eJ.inv).hom.app (F.op.obj U)
      ((constantPullbackIso F J K hW hFW A).hom.hom.app (F.op.obj U)
        (eK.hom.hom.app (F.op.obj U)
          (φ.hom.app U (eJ.inv.hom.app U
            ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a))))) =
      (adj.unit.app (UJ.obj R)).hom.app U
        (eJ.inv.hom.app U ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a))
    rw [hiJ]
    change (φ.hom.app U)
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a) =
        (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of A))).app (F.op.obj U) a at hp
    rw [hp]
    change eK.hom.hom.app (F.op.obj U)
      ((toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of A))).app (F.op.obj U) a) =
        (toSheafify K ((Functor.const Dᵒᵖ).obj A)).app (F.op.obj U) a at hk
    rw [hk]
    change (constantPullbackIso F J K hW hFW A).hom.hom.app (F.op.obj U)
      ((toSheafify K ((Functor.const Dᵒᵖ).obj A)).app (F.op.obj U) a) =
        (adj.unit.app ((constantSheaf J (Type u)).obj A)).hom.app U
          ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a) at hc
    rw [hc]
    have hh := ConcreteCategory.congr_hom hn
      ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a)
    change (adj.unit.app (UJ.obj R)).hom.app U
      (eJ.inv.hom.app U ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a)) = _ at hh
    rw [hiJ] at hh
    exact hh.symm
  intro U x
  exact congrArg (fun t ↦ t.hom.app U x) he

end ConstantPresentation

section AbelianComparison
variable (S : Scheme.{u})
-- The source affine Kan-extension argument with the coefficient universe kept independent.
private theorem additivePreservesRelative (F : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{max v (u + 1)}) :
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

private theorem additiveIsSheaf (F : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{max v (u + 1)})
    (hF : Presheaf.IsSheaf (smallEtaleTopology S) F) :
    Presheaf.IsSheaf (AffineProEt.topology S)
      ((AffineProEt.toProEt S).op ⋙ (Scheme.toProEt S).op.lan.obj F) := by
  let _ := additivePreservesRelative S F
  let _ : HasFilteredColimitsOfSize.{u, u} AddCommGrpCat.{max v (u + 1)} :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, max v (u + 1), max v (u + 1)}
  let _ : AB5OfSize.{u, u} AddCommGrpCat.{max v (u + 1)} :=
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

-- Override the successor-universe-only source instance locally in this section.
private instance (priority := 100000) largeAbSheafify {C : Type*} [Category C]
    [EssentiallySmall.{w} C] (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{w} := by
  let e := equivSmallModel.{w} C
  have : HasSheafify (e.inverse.inducedTopology J) AddCommGrpCat.{w} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  exact e.hasSheafify J (e.inverse.inducedTopology J) _

private theorem additiveUnitIso :
    IsIso (sheafAdjunctionContinuous (toProEt S) AddCommGrpCat.{max v (u + 1)}
      S.smallEtaleTopology (ProEt.topology S)).unit := by
  let A := AddCommGrpCat.{max v (u + 1)}
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
  have h2 : IsIso ((AffineProEt.toProEt S).op.whiskerLeft
      (toSheafify (ProEt.topology S) ((toProEt S).op.lan.obj F.obj))) :=
    Functor.IsDenseSubsite.isIso_whiskerLeft_toSheafify (AffineProEt.topology S) _ _ A _
      (additiveIsSheaf S F.obj F.property)
  have h3 : IsIso ((AffineEtale.Spec S).op.whiskerLeft ((toProEt S).op.whiskerLeft
      (toSheafify (ProEt.topology S) ((toProEt S).op.lan.obj F.obj)))) := by
    rw [NatTrans.isIso_iff_isIso_app] at h2 ⊢
    intro U
    exact h2 (Opposite.op ((AffineEtale.toAffineProEt S).obj U.unop))
  infer_instance

private theorem smallModelAbFaithful (X : Scheme.{u}) :
    (sheafPullback (Scheme.smallModelComparisonInclusion.{u, v} X)
      AddCommGrpCat.{max v (u + 1)} (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).Faithful := by
  let A := AddCommGrpCat.{max v (u + 1)}
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
  have : IsIso adjL.unit := additiveUnitIso.{u, v} X
  have : L.Faithful := adjL.faithful_L_of_mono_unit_app
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
  exact Functor.Faithful.of_iso q

end AbelianComparison

private theorem comparisonUnderlying (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    Nonempty (constructibleComparisonPullback X A ⋙ SheafOfModules.toSheaf _ ≅
        SheafOfModules.toSheaf _ ⋙
          sheafPullback (Scheme.smallModelComparisonInclusion.{u, v} X)
            AddCommGrpCat.{max v (u + 1)}
            (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
            (Scheme.coefficientProEtaleModelTopology.{u, v} X)) := by
  let F := Scheme.smallModelComparisonInclusion.{u, v} X
  let J := Scheme.smallModelComparisonEtaleTopology.{u, v} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  have : (AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).isEquivalence_inverse
  have : (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).isEquivalence_functor
  have : PreservesFiniteLimits F := by
    dsimp [F, Scheme.smallModelComparisonInclusion]
    infer_instance
  let W := ⊤_ (Scheme.smallModelComparisonEtaleSite.{u, v} X)
  have hW : IsTerminal W := terminalIsTerminal
  have hFW : IsTerminal (F.obj W) := hW.isTerminalObj F W
  have : RepresentablyFlat F := by
    dsimp [F, Scheme.smallModelComparisonInclusion]
    infer_instance
  obtain ⟨pr, hpr⟩ := ringPresentation F J K hW hFW A
  obtain ⟨e, _⟩ := SheafOfModules.inverseImage_underlying_unit_of_ring_presentation
    (F := F) (constructibleComparisonRingMap X A) pr hpr
  exact ⟨e⟩

/-- The canonical constant-coefficient comparison on intrinsic module sheaves is
left exact and faithful, in the full coefficient universe.
Source: Stacks Project, Tags 00YV (6) and 099T; blueprint comparison on classical
module sheaves (auxiliary; not a blueprint node).

Proof: first construct the constant-set pullback isomorphism by uniqueness of the
constant-sheaf and comparison adjunctions. Its unit equation at the terminal object,
then naturality, show that it sends every constant section to the same constant.
Commute the underlying-set functor with constant sheafification. The resulting ring
presentation has exactly constructibleComparisonRingMap as its unit. Apply the
module inverse-image unit comparison to identify the underlying additive sheaf of
the canonical module pullback with the abelian-sheaf pullback. Representable flatness
of the site inclusion and exact filtered colimits imply left exactness of that
abelian pullback; the module forgetful functor reflects finite limits.

For faithfulness, repeat the proved comparison-unit argument with additive sheaves
in universe max v (u+1). On the affine pro-etale basis the Kan extension is already a
sheaf: it carries the standard cofiltered presentations to filtered colimits, and
filtered colimits of abelian groups are exact. Density of the affine basis shows
that sheafification preserves its affine etale sections. Full faithfulness of the
etale inclusion makes the Kan-extension unit invertible there, so the comparison
unit is invertible. Transport this faithful abelian comparison through the AsSmall
site equivalences, identify its left adjoint with the small-model pullback by
uniqueness, and use the underlying additive-sheaf comparison to reflect equality of
module morphisms. This argument applies to the zero ring and the empty scheme and
needs no Noetherianity or constructibility. -/
theorem constructibleComparisonPullback_exact_faithful (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    PreservesFiniteLimits (constructibleComparisonPullback X A) ∧
      (constructibleComparisonPullback X A).Faithful := by
  let F := constructibleComparisonPullback X A
  let V := SheafOfModules.toSheaf.{max v (u + 1)} (siteModuleRings (ConstantCompletion.constant
    (Scheme.coefficientProEtaleModelTopology.{u, v} X) A))
  let L := sheafPullback (Scheme.smallModelComparisonInclusion.{u, v} X)
    AddCommGrpCat.{max v (u + 1)} (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)
  have : (AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).isEquivalence_inverse
  have : (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).isEquivalence_functor
  have : RepresentablyFlat (Scheme.smallModelComparisonInclusion.{u, v} X) := by
    dsimp [Scheme.smallModelComparisonInclusion]
    infer_instance
  have : PreservesFiniteLimits L := by
    dsimp [L]
    infer_instance
  have : L.Faithful := smallModelAbFaithful.{u, v} X
  obtain ⟨e⟩ := comparisonUnderlying X A
  have : PreservesFiniteLimits (F ⋙ V) := preservesFiniteLimits_of_natIso e.symm
  have : (F ⋙ V).Faithful := Functor.Faithful.of_iso e.symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F V,
    Functor.Faithful.of_comp F V⟩

end AlgebraicGeometry.ProEtale
