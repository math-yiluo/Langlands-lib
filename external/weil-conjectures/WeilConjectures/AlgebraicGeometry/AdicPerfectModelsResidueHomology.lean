/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
import WeilConjectures.AlgebraicGeometry.AdicResidueLocalHomologyComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparison
import WeilConjectures.AlgebraicGeometry.FiniteComparisonModelRealization
import WeilConjectures.AlgebraicGeometry.NoetherianGlobalConstructibility
import WeilConjectures.ConstructibleSheaf.InternalHom

/-! # Constructible etale origin of individual residue cohomology sheaves

Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u c d h k w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

namespace AdicResidueDescent

private def leftSquareOfRight
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    (L' : E ⥤ H) (R' : H ⥤ E) (adj' : L' ⊣ R')
    (F : C ≌ E) (G : D ≌ H) (i : R ⋙ F.functor ≅ G.functor ⋙ R') :
    L ⋙ G.functor ≅ F.functor ⋙ L' := by
  let a := adj.comp G.toAdjunction
  let b := F.toAdjunction.comp adj'
  let h : (G.inverse ⋙ R) ⋙ F.functor ≅ R' :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft G.inverse i ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight G.counitIso R' ≪≫ Functor.leftUnitor R'
  let h' : (R' ⋙ F.inverse) ⋙ F.functor ≅ R' :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft R' F.counitIso ≪≫
      Functor.rightUnitor R'
  let r := ((Functor.FullyFaithful.ofFullyFaithful F.functor).whiskeringRight _)
    |>.preimageIso (h ≪≫ h'.symm)
  exact ((conjugateIsoEquiv a b).symm r).symm

private def localFinite {C : Type c} [Category.{h} C]
    (J : GrothendieckTopology C) (A : Type w) [CommRing A]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{w} A)]
    (F : Sheaf J (ModuleCat.{w} A)) : Prop :=
  ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧ ∀ (U : C) (f : U ⟶ V), S f →
    ∃ M : ModuleCat.{w} A, Module.Finite A M ∧
      Nonempty (F.over U ≅ (constantSheaf (J.over U) (ModuleCat.{w} A)).obj M)

private theorem localFinite_precomp
    {C : Type c} {D : Type d} [Category.{h} C] [Category.{k} D]
    [HasPullbacks C] [HasPullbacks D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (G : C ⥤ D) [G.IsEquivalence] [G.IsContinuous J K] [G.IsCocontinuous J K]
    (A : Type w) [CommRing A]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{w} A)]
    [∀ V : D, HasSheafify (K.over V) (ModuleCat.{w} A)]
    [HasLimitsOfSize.{h, max c h k} (ModuleCat.{w} A)]
    (F : Sheaf K (ModuleCat.{w} A)) (hF : localFinite K A F) :
    localFinite J A ((G.sheafPushforwardContinuous (ModuleCat.{w} A) J K).obj F) := by
  let : G.PreservesOneHypercovers J K :=
    Functor.PreservesOneHypercovers.of_coverPreserving
      (CoverPreserving.of_isContinuous G J K)
  intro V
  obtain ⟨S, hS, hm⟩ := hF (G.obj V)
  refine ⟨S.functorPullback G, G.cover_lift J K hS, fun U f hf ↦ ?_⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := hm (G.obj U) (G.map f) hf
  let H : Over U ⥤ Over (G.obj U) := Over.post G
  let r : ((G.sheafPushforwardContinuous (ModuleCat.{w} A) J K).obj F).over U ≅
      (H.sheafPushforwardContinuous (ModuleCat.{w} A)
        (J.over U) (K.over (G.obj U))).obj (F.over (G.obj U)) :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  let ce := (H.pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{w} A) (J.over U) (K.over (G.obj U))).symm.app
      ((Functor.const (Over (G.obj U))ᵒᵖ).obj M)
  exact ⟨M, hM, ⟨r ≪≫
    (H.sheafPushforwardContinuous (ModuleCat.{w} A)
      (J.over U) (K.over (G.obj U))).mapIso e ≪≫ ce⟩⟩

private theorem localFinite_iso
    {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
    (A : Type w) [CommRing A]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{w} A)]
    {F G : Sheaf J (ModuleCat.{w} A)} (e : F ≅ G) (hF : localFinite J A F) :
    localFinite J A G := by
  intro V
  obtain ⟨S, hS, hm⟩ := hF V
  refine ⟨S, hS, fun U f hf ↦ ?_⟩
  obtain ⟨M, hM, ⟨i⟩⟩ := hm U f hf
  exact ⟨M, hM, ⟨(J.overPullback (ModuleCat.{w} A) U).mapIso e.symm ≪≫ i⟩⟩

private theorem localFinite_site_equivalence
    {C : Type c} {D : Type d} [Category.{h} C] [Category.{k} D]
    [HasPullbacks C] [HasPullbacks D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (e : C ≌ D)
    [e.inverse.IsDenseSubsite K J] (A : Type w) [CommRing A]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{w} A)]
    [∀ V : D, HasSheafify (K.over V) (ModuleCat.{w} A)]
    [HasLimitsOfSize.{h, max c h k} (ModuleCat.{w} A)]
    [HasLimitsOfSize.{k, max d k h} (ModuleCat.{w} A)]
    (F : Sheaf J (ModuleCat.{w} A)) :
    localFinite J A F ↔ localFinite K A ((e.sheafCongr J K (ModuleCat.{w} A)).functor.obj F) := by
  constructor
  · exact localFinite_precomp K J e.inverse A F
  · intro hF
    have hh := localFinite_precomp J K e.functor A
      ((e.sheafCongr J K (ModuleCat.{w} A)).functor.obj F) hF
    exact localFinite_iso J A ((e.sheafCongr J K (ModuleCat.{w} A)).unitIso.app F).symm hh

private def finiteModelSieve {C : Type c} [Category.{h} C]
    (J : GrothendieckTopology C) (A : Type w) [CommRing A]
    [HasSheafify J (ModuleCat.{w} A)]
    (F : Sheaf J (ModuleCat.{w} A)) (V : C) : Sieve V where
  arrows U _ := ∃ M : ModuleCat.{w} A, Module.Finite A M ∧
    Nonempty (F.over U ≅ ((constantSheaf J (ModuleCat.{w} A)).obj M).over U)
  downward_closed := by
    rintro U W f ⟨M, hM, ⟨e⟩⟩ g
    let G := (constantSheaf J (ModuleCat.{w} A)).obj M
    exact ⟨M, hM, ⟨(F.pushforwardOverMapIso g).symm ≪≫
      (J.overMapPullback (ModuleCat.{w} A) g).mapIso e ≪≫ G.pushforwardOverMapIso g⟩⟩

private theorem localFinite_iff_sieve
    {C : Type c} [Category.{h} C] [HasTerminal C]
    (J : GrothendieckTopology C) (A : Type w) [CommRing A]
    [HasSheafify J (ModuleCat.{w} A)]
    [∀ U : C, HasSheafify (J.over U) (ModuleCat.{w} A)]
    [∀ (U : C) (P : (Over U)ᵒᵖ ⥤ ModuleCat.{w} A),
      (Over.forget U).op.HasPointwiseRightKanExtension P]
    (F : Sheaf J (ModuleCat.{w} A)) :
    localFinite J A F ↔ finiteModelSieve J A F (⊤_ C) ∈ J (⊤_ C) := by
  constructor
  · intro hf
    obtain ⟨S, hS, hm⟩ := hf (⊤_ C)
    apply J.superset_covering _ hS
    intro U f hf
    obtain ⟨M, hM, ⟨e⟩⟩ := hm U f hf
    exact ⟨M, hM, ⟨e ≪≫ ((J.overPullbackConstantSheafIso (ModuleCat.{w} A) U).app M).symm⟩⟩
  · intro hf V
    refine ⟨(finiteModelSieve J A F (⊤_ C)).pullback (terminal.from V),
      J.pullback_stable _ hf, fun U f hf ↦ ?_⟩
    obtain ⟨M, hM, ⟨e⟩⟩ := hf
    exact ⟨M, hM, ⟨e ≪≫ (J.overPullbackConstantSheafIso (ModuleCat.{w} A) U).app M⟩⟩

private def etaleSites (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    Sheaf (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) (ModuleCat.{u + 1} A) ≌
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.Etale)
  letI : (AsSmall.down : AsSmall.{u + 1} X.Etale ⥤ X.Etale).IsEquivalence :=
    e.isEquivalence_inverse
  letI : e.inverse.IsDenseSubsite
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) X.smallEtaleTopology :=
    inferInstanceAs ((AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, u + 1} X ⥤
      X.Etale).IsDenseSubsite
        ((AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, u + 1} X ⥤
          X.Etale).inducedTopology X.smallEtaleTopology) X.smallEtaleTopology)
  exact (e.sheafCongr X.smallEtaleTopology
    (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) (ModuleCat.{u + 1} A)).symm

private theorem etaleSites_localFinite
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (F : Sheaf (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X)
      (ModuleCat.{u + 1} A)) :
    IsCoefficientModelLocallyConstantFinite _ A F ↔
      localFinite X.smallEtaleTopology A ((etaleSites X A).functor.obj F) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.Etale)
  let : (AsSmall.down : AsSmall.{u + 1} X.Etale ⥤ X.Etale).IsEquivalence :=
    e.isEquivalence_inverse
  let : e.inverse.IsDenseSubsite
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) X.smallEtaleTopology :=
    inferInstanceAs ((AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, u + 1} X ⥤
      X.Etale).IsDenseSubsite
        ((AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, u + 1} X ⥤
          X.Etale).inducedTopology X.smallEtaleTopology) X.smallEtaleTopology)
  let : e.functor.IsDenseSubsite X.smallEtaleTopology
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) := by
    infer_instance
  let : e.symm.inverse.IsDenseSubsite X.smallEtaleTopology
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) :=
    inferInstanceAs (e.functor.IsDenseSubsite _ _)
  let : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} A) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}
  exact localFinite_site_equivalence _ _ e.symm A F

private def etaleSitePullbackSquare {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] :
    Scheme.coefficientEtaleFixedPullback.{u, u + 1} f A ⋙ (etaleSites X A).functor ≅
      (etaleSites Y A).functor ⋙ Etale.upperStar (ModuleCat.{u + 1} A) f := by
  let R := (Scheme.coefficientEtaleBaseChange.{u, u + 1} f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} A) (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} Y)
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X)
  let i : R ⋙ (etaleSites Y A).functor ≅
      (etaleSites X A).functor ⋙ Etale.lowerStar (ModuleCat.{u + 1} A) f :=
    NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _
      (NatIso.ofComponents (fun U ↦ Iso.refl _)))
  exact leftSquareOfRight _ R
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _)
    _ _ (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (etaleSites Y A) (etaleSites X A) i

private def proSites (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) (ModuleCat.{u + 1} A) ≌
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)
  letI : (AsSmall.down : AsSmall.{u + 1} X.ProEt ⥤ X.ProEt).IsEquivalence :=
    e.isEquivalence_inverse
  letI : e.inverse.IsDenseSubsite
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) (Scheme.ProEt.topology X) :=
    inferInstanceAs ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u + 1} X ⥤
      X.ProEt).IsDenseSubsite
        ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u + 1} X ⥤
          X.ProEt).inducedTopology (Scheme.ProEt.topology X)) (Scheme.ProEt.topology X))
  exact (e.sheafCongr (Scheme.ProEt.topology X)
    (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) (ModuleCat.{u + 1} A)).symm

private theorem proSites_localFinite
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X)
      (ModuleCat.{u + 1} A)) :
    IsCoefficientModelLocallyConstantFinite _ A F ↔
      localFinite (Scheme.ProEt.topology X) A ((proSites X A).functor.obj F) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)
  let : (AsSmall.down : AsSmall.{u + 1} X.ProEt ⥤ X.ProEt).IsEquivalence :=
    e.isEquivalence_inverse
  let : e.inverse.IsDenseSubsite
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) (Scheme.ProEt.topology X) :=
    inferInstanceAs ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u + 1} X ⥤
      X.ProEt).IsDenseSubsite
        ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u + 1} X ⥤
          X.ProEt).inducedTopology (Scheme.ProEt.topology X)) (Scheme.ProEt.topology X))
  let : e.functor.IsDenseSubsite (Scheme.ProEt.topology X)
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) := by
    infer_instance
  let : e.symm.inverse.IsDenseSubsite (Scheme.ProEt.topology X)
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) :=
    inferInstanceAs (e.functor.IsDenseSubsite _ _)
  let : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} A) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}
  exact localFinite_site_equivalence _ _ e.symm A F

private def proSitePullbackSquare {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] :
    Scheme.coefficientProEtaleFixedModulePullback.{u, u + 1} f A ⋙ (proSites X A).functor ≅
      (proSites Y A).functor ⋙ ProEtale.upperStar (ModuleCat.{u + 1} A) f := by
  let R := (Scheme.coefficientProEtaleModelBaseChange.{u, u + 1} f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} A) (Scheme.coefficientProEtaleModelTopology.{u, u + 1} Y)
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X)
  let i : R ⋙ (proSites Y A).functor ≅
      (proSites X A).functor ⋙ ProEtale.lowerStar (ModuleCat.{u + 1} A) f :=
    NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _
      (NatIso.ofComponents (fun U ↦ Iso.refl _)))
  exact leftSquareOfRight _ R
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _)
    _ _ (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (proSites Y A) (proSites X A) i

end AdicResidueDescent

private theorem finiteLocallyConstant_of_localModels
    (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (h : AdicResidueDescent.localFinite X.smallEtaleTopology A F) :
    IsFiniteLocallyConstantSheaf F := by
  classical
  have hS := (AdicResidueDescent.localFinite_iff_sieve X.smallEtaleTopology A F).mp h
  let T : X.Etale := Etale.mk (𝟙 X)
  let S := AdicResidueDescent.finiteModelSieve X.smallEtaleTopology A F T
  have hmem : AdicResidueDescent.finiteModelSieve X.smallEtaleTopology A F (⊤_ X.Etale) ∈
      X.smallEtaleTopology (⊤_ X.Etale) ↔ S ∈ X.smallEtaleTopology T := by
    let e := (Etale.isTerminalMkId X).uniqueUpToIso terminalIsTerminal
    change _ ↔ (AdicResidueDescent.finiteModelSieve X.smallEtaleTopology A F
      (⊤_ X.Etale)).pullback e.hom ∈ X.smallEtaleTopology T
    exact GrothendieckTopology.pullback_mem_iff_of_isIso.symm
  have hx := (mem_smallEtaleTopology_iff S).mp (hmem.mp hS)
  choose V g hg hx using hx
  have hc : ∀ x : X, ∃ i y, (V i).hom y = x := by
    intro x
    obtain ⟨y, hy⟩ := hx x
    have hw : (g x).left = (V x).hom :=
      (Category.comp_id _).symm.trans (MorphismProperty.Over.w (g x))
    exact ⟨x, y, (congrArg (fun f : (V x).left ⟶ X ↦ f y) hw.symm).trans hy⟩
  let C : Cover.{u} etalePrecoverage X :=
    Cover.mkOfCovers X (fun x ↦ (V x).left) (fun x ↦ (V x).hom) hc
  have hm (i : C.I₀) : ∃ M : ModuleCat.{u + 1} A, Module.Finite A M ∧
      Nonempty (F.over (C.etalePrecoverageToEtale i) ≅
        (constantSheaf (X.smallEtaleTopology.over (C.etalePrecoverageToEtale i))
          (ModuleCat.{u + 1} A)).obj M) := by
    obtain ⟨M, hM, ⟨e⟩⟩ := hg i
    exact ⟨M, hM, ⟨e ≪≫ (X.smallEtaleTopology.overPullbackConstantSheafIso
      (ModuleCat.{u + 1} A) (V i)).app M⟩⟩
  have (i : C.I₀) : IsFiniteSheaf ((Etale.upperStar (ModuleCat.{u + 1} A)
      (C.f i)).obj F) := by
    obtain ⟨M, hM, ⟨e⟩⟩ := hm i
    let := hM
    have := isFiniteSheaf_constantSheaf
      (X := (C.etalePrecoverageToEtale i).left) M
    let ec := ((Etale.overEquiv (C.etalePrecoverageToEtale i)).constantSheafSheafCongrIso
      (X.smallEtaleTopology.over (C.etalePrecoverageToEtale i))
      (C.etalePrecoverageToEtale i).left.smallEtaleTopology
      (ModuleCat.{u + 1} A) Over.mkIdTerminal).app M
    let ei := (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} A)
      (C.etalePrecoverageToEtale i) F).symm ≪≫
      (Etale.overSheafEquiv (C.etalePrecoverageToEtale i)
        (ModuleCat.{u + 1} A)).functor.mapIso e ≪≫ ec
    exact IsFiniteSheaf.of_iso ei.symm
  exact
    { toIsLocallyConstantSheaf := ⟨⟨⟨C, fun i ↦ by
        obtain ⟨M, _, ⟨e⟩⟩ := hm i
        exact Sheaf.isConstant_of_iso _ e⟩⟩⟩
      toIsFiniteSheaf := IsFiniteSheaf.of_cover C F }

private theorem constructible_of_coefficientModel (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (G : ConstantCompletion.Mod (ConstantCompletion.constant
      (smallModelComparisonEtaleTopology.{u, u + 1} X) A))
    (hG : IsCoefficientConstructibleEtaleModule.{u, u + 1} X A G) :
    IsConstructibleSheaf ((ProEtale.finiteComparisonEtaleModelRealization X A).obj G) := by
  obtain ⟨S, _, hS⟩ := (etale_noetherian_global_constructibility.{u, u + 1} X A G).mp hG
  refine ⟨S, fun i ↦ ?_⟩
  have h := (AdicResidueDescent.etaleSites_localFinite (S.domain i) A _).mp (hS i)
  let e := (AdicResidueDescent.etaleSitePullbackSquare (S.immersion i) A).app
    ((coefficientModelFixedScalars.{u + 1} _ A).obj G)
  apply finiteLocallyConstant_of_localModels
  exact AdicResidueDescent.localFinite_iso _ A e h

private theorem etaleOrigin_of_stratifiedModels (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))
    (S : Stratification X)
    (hS : ∀ i : Fin S.n, AdicResidueDescent.localFinite (ProEt.topology (S.domain i)) A
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj F)) :
    ∃ G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
      IsConstructibleSheaf G ∧
        Nonempty ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).obj G ≅ F) := by
  let R := ProEtale.finiteComparisonProEtaleModelRealization X A
  let M := R.objPreimage F
  have he : R.obj M ≅ F := R.objObjPreimageIso F
  have hM : IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, u + 1} X A M := by
    apply (proEtale_noetherian_global_constructibility.{u, u + 1} X A M).mpr
    refine ⟨S, S.isConstructible_stratum, ?_⟩
    intro i V
    have hh : IsCoefficientModelLocallyConstantFinite _ A
        ((coefficientProEtaleFixedModulePullback.{u, u + 1} (S.immersion i) A).obj
          ((coefficientModelFixedScalars.{u + 1} _ A).obj M)) := by
      apply (AdicResidueDescent.proSites_localFinite (S.domain i) A _).mpr
      let e := (AdicResidueDescent.proSitePullbackSquare (S.immersion i) A).app
        ((coefficientModelFixedScalars.{u + 1} _ A).obj M)
      apply AdicResidueDescent.localFinite_iso _ A e.symm
      exact AdicResidueDescent.localFinite_iso _ A
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) (S.immersion i)).mapIso he).symm (hS i)
    obtain ⟨T, hT, hm⟩ := hh V
    refine ⟨T, hT, fun W f hf ↦ ?_⟩
    obtain ⟨N, hN, e⟩ := hm W f hf
    let := hN
    exact ⟨N, Module.finitePresentation_of_finite A N, e⟩
  obtain ⟨E, ⟨eE⟩⟩ := (ProEtale.constructibleComparison.{u, u + 1} X A).2.2.1
  let M' : ObjectProperty.FullSubcategory
      (IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, u + 1} X A) := ⟨M, hM⟩
  let G := E.inverse.obj M'
  let eg : (ProEtale.constructibleComparisonPullback.{u, u + 1} X A).obj G.obj ≅ M :=
    (eE.app G).symm ≪≫
      (ObjectProperty.ι
      (IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, u + 1} X A)).mapIso
        (E.counitIso.app M')
  obtain ⟨es⟩ := ProEtale.finiteComparisonModelPullbackSquare X A
  exact ⟨(ProEtale.finiteComparisonEtaleModelRealization X A).obj G.obj,
    constructible_of_coefficientModel X A G.obj G.property,
    ⟨(es.app G.obj).symm ≪≫ R.mapIso eg ≪≫ he⟩⟩

/-- Each residue cohomology sheaf has a constructible etale antecedent.
This is a statement about sheaves; it does not descend a derived object.
Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication; Lemma 6.3.13;
Stacks Tags 09AJ and 09AK.
(auxiliary; not a blueprint node).

Proof: restrict the canonical residue to the given covering slices of each stratum.
The finite-projection scalar comparison and exact fixed-scalar restriction commute
with cohomology. Apply adicPerfectModel_complete_reduction to the local perfect
coefficient complex P. Its residue cohomology is the constant realization of
H^q(P tensor_A A/I), which is a finite-dimensional A/I-vector space and therefore
finitely presented. Transport that constant model along the local isomorphism for K.
Thus the residue cohomology is intrinsically constructible on the given finite
stratification. The Noetherian global-constructibility theorem identifies this with
affine-local constructibility. The sheaf part of constructibleComparison then
supplies a constructible etale module and its comparison isomorphism. Transport
through the constant-scalar equivalence and the small-site equivalences; their
units retain constant sections, giving exactly the displayed comparisonUpperStar.
This argument allows infinite residue fields and varying finite module ranks.
Empty schemes and zero cohomology sheaves give the zero etale module. -/
theorem adicPerfectModels_residueHomology (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.IsMaximal ∧ ∀ J : Ideal A, J.IsMaximal → J = I)
    [IsAdicComplete I A]
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (hK : IsSfbStratifiedPerfect X I K) :
    ∀ q : ℤ, ∃ G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))),
      IsConstructibleSheaf G ∧
        Nonempty ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) X).obj G ≅
          (DerivedCategory.homologyFunctor _ q).obj
            (DerivedCategory.Q.obj (sfbResidueComplex X I K))) := by
  classical
  obtain ⟨S, _, hS⟩ := hK
  intro q
  apply etaleOrigin_of_stratifiedModels X (A ⧸ I ^ (0 + 1)) _ S
  intro i
  obtain ⟨V, hV, hmodels⟩ := hS i
  apply (AdicResidueDescent.localFinite_iff_sieve _ _ _).mpr
  apply (ProEt.topology (S.domain i)).superset_covering _ hV
  intro U f hf
  obtain ⟨P, a, b, _, hge, hle, hP, he⟩ := hmodels U f hf
  let := hge
  let := hle
  have hb (n : ℤ) (hn : n < a ∨ b < n) : IsZero (P.X n) := by
    rcases hn with hn | hn
    · exact P.isZero_of_isStrictlyGE a n hn
    · exact P.isZero_of_isStrictlyLE b n hn
  have hp (n : ℤ) : Module.Finite A (P.X n) ∧ Module.Projective A (P.X n) :=
    ⟨(hP n).2, (hP n).1⟩
  obtain ⟨_, _, hfinite, _⟩ :=
    adicPerfectModel_complete_reduction.{u, u + 1} X A I hI.1 P a b hb hp
  obtain ⟨e⟩ := adicResidue_localModelComparison (S.immersion i) A I hI.1
    K U P a b hb hp he
  let L := ProEtale.upperStar (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) (S.immersion i) ⋙
    (ProEt.topology (S.domain i)).overPullback
      (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) U
  let : L.Additive := Functor.additive_of_preserves_binary_products L
  let C := constantSheaf ((ProEt.topology (S.domain i)).over U)
    (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))
  let : C.Additive := Functor.additive_of_preserves_binary_products C
  let P' := AdicPerfectModel.algebraicResidue I P
  let eh := (L.mapDerivedCategoryHomologyFunctorIso q).app
      (DerivedCategory.Q.obj (sfbResidueComplex X I K)) ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors _ q).app
      ((C.mapHomologicalComplex (.up ℤ)).obj P') ≪≫
    (P'.sc q).mapHomologyIso C
  exact ⟨P'.homology q, hfinite q,
    ⟨eh ≪≫ (((ProEt.topology (S.domain i)).overPullbackConstantSheafIso
      (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) U).app _).symm⟩⟩

end AlgebraicGeometry.Scheme
