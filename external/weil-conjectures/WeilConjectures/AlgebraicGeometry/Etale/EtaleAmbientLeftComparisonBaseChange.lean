/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange
import WeilConjectures.AlgebraicGeometry.Etale.EtaleNormalizedMatesCompositionPasting
import WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Subsheaf
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
import WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.EtaleSupportExchange.EtaleSupportExchangeRightMate

/-! # Base change of the etale compact-support composition comparison

The comparison below concerns the left adjoints, before taking a mate or evaluating at
coefficients. It uses the actual graph-normalized sum-extension comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar lowerStar
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  canonicalEtaleCompactSupportComparison derivedEtaleLowerShriekUpperStarAdjunction

private theorem normalization_refinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c d : Compactification e) (r : c.Refinement d) :
    (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
      (N.comparison e d).hom = (N.comparison e c).hom := by
  have : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  have h := N.refinement e c d r
  have hr := unboundedEtaleCompactSupport_refinement_normalization A e r N
  have hc := unboundedEtaleCompactSupport_comparison_coherence A e
  have hdc : (rightDerivedLowerShriekOfCompactificationIso A d c).hom ≫
      (N.comparison e c).hom = (N.comparison e d).hom := by
    rw [hr]
    dsimp only [unboundedEtaleRefinementOpenComparison, Iso.symm_hom]
    simpa only [Category.assoc] using h
  rw [← hdc, ← Category.assoc]
  have hi : (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
      (rightDerivedLowerShriekOfCompactificationIso A d c).hom = 𝟙 _ := by
    exact congrArg Iso.hom ((hc.2 c d c).trans (hc.1 c))
  rw [hi, Category.id_comp]

private theorem normalization_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c d : Compactification e) :
    (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
      (N.comparison e d).hom = (N.comparison e c).hom := by
  have hc := normalization_refinement A N e (Compactification.inf c d) c
    (Compactification.infFst c d)
  have hd := normalization_refinement A N e (Compactification.inf c d) d
    (Compactification.infSnd c d)
  apply (cancel_epi
    (rightDerivedLowerShriekOfCompactificationIso A (Compactification.inf c d) c).hom).1
  rw [← Category.assoc, ← Iso.trans_hom,
    (unboundedEtaleCompactSupport_comparison_coherence A e).2, hd]
  exact hc.symm

private theorem left_comparison_chosen
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U X B : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian B]
    (e : U ⟶ X) (f : X ⟶ B) [Etale e] [IsSeparated e] [QuasiCompact e]
    [HasCompactification e] [HasCompactification f] [HasCompactification (e ≫ f)]
    [QuasiCompact (e ≫ f)] :
    etaleAmbientLeftComparison A N e f (HasCompactification.compactification f)
        (HasCompactification.compactification (e ≫ f)) =
      Functor.isoWhiskerRight
        (N.comparison e (HasCompactification.compactification e)).symm
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) ≪≫
      unboundedEtaleLowerShriekCompIso A e f := by
  let c : Compactification e := HasCompactification.compactification e
  let d : Compactification e := ((HasCompactification.compactification (e ≫ f)).ofComp
    (HasCompactification.compactification f)).restrict
  have hc : rightDerivedLowerShriekOfCompactificationIso A d c ≪≫
      N.comparison e c = N.comparison e d :=
    Iso.ext (normalization_comparison A N e d c)
  have h := (congrArg Iso.inv hc).symm
  dsimp only [Iso.trans_inv, c, d] at h
  apply Iso.ext
  simp only [etaleAmbientLeftComparison, unboundedEtaleLowerShriekCompIso,
    rightDerivedLowerShriekIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, h, Functor.whiskerRight_comp,
    rightDerivedLowerShriek, Category.assoc]

private lemma mono_compactification_to_star_aux
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
    {U X : Scheme.{u}} {f : U ⟶ X} (c : Compactification f)
    (F : Sheaf U.smallEtaleTopology B)
    [Mono ((openImmersionLowerShriekToLowerStar B c.i).app F)] :
    Mono ((lowerStar B c.g).map ((openImmersionLowerShriekToLowerStar B c.i).app F) ≫
      (lowerStarComp B c.i c.g f c.comm).hom.app F) := by
  infer_instance

-- The normalization equations force the explicit graph comparison. This reduces the
-- geometric tower calculation to the constructed graph maps, independently of N.
private lemma normalization_comparison_eq_canonical
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f] [QuasiCompact f]
    [IsNoetherian U] [IsNoetherian X] (c : Compactification f) :
    N.comparison f c = canonicalEtaleCompactSupportComparison A f c := by
  have hm (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      Mono ((compactificationSheafToDirectImage A c).app F) := by
    have ho (V : c.Z.Etaleᵒᵖ) :
        Mono (((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app F
          ).hom.app V) :=
      ConcreteCategory.mono_of_injective _
        (openExtensionProperSupport_range A c.i F V.unop).1
    have : Mono
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app F).hom :=
      NatTrans.mono_of_mono_app _
    have : Mono ((openImmersionLowerShriekToLowerStar
        (ModuleCat.{u + 1} A) c.i).app F) :=
      Sheaf.Hom.mono_of_presheaf_mono c.Z.smallEtaleTopology (ModuleCat.{u + 1} A) _
    exact mono_compactification_to_star_aux (ModuleCat.{u + 1} A) c F
  let core := canonicalEtaleCompactSupportCore A
  have hs : N.sheafComparison f c = core.sheafComparison f c := by
    apply NatTrans.ext
    funext F
    apply (cancel_mono ((compactificationSheafToDirectImage A c).app F)).1
    rw [N.sheaf_normalization, core.sheaf_normalization]
  change N.comparison f c = core.comparison f c
  apply Iso.ext_inv
  apply (Functor.whiskeringLeft _ _ _).obj DerivedCategory.Qh |>.map_injective
  apply NatTrans.ext
  funext K
  change (N.comparison f c).inv.app (DerivedCategory.Qh.obj K) =
    (core.comparison f c).inv.app (DerivedCategory.Qh.obj K)
  rw [N.derived_normalization, core.derived_normalization, hs]

private theorem normalized_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {w : X' ⟶ X} {w' : U' ⟶ U}
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e']
    [QuasiCompact e] [QuasiCompact e']
    (sq : IsPullback w' e' e w) (c : Compactification e) (d : Compactification e')
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (G' : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ G')
    (K : DerivedCategoryModule A X) :
    (etaleNormalizedRightExchange A sq c d G G' adj adj').app K ≫
        (EtaleSupportExchange.rightAdjointIso A e' d G' adj').hom.app
          ((upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.obj K) =
      (upperStar (ModuleCat.{u + 1} A) w').mapDerivedCategory.map
          ((EtaleSupportExchange.rightAdjointIso A e c G adj).hom.app K) ≫
        (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).inv.app K := by
  have : IsNoetherian (pullback w e) :=
    isNoetherian_of_locallyOfFiniteType (pullback.fst w e)
  let e₀ := pullback.fst w e
  let w₀ := pullback.snd w e
  let sq₀ := (IsPullback.of_hasPullback w e).flip
  let c₀ := c.ofIsPullback sq₀
  let G₀ := (upperStar (ModuleCat.{u + 1} A) e₀).mapDerivedCategory
  let adj₀ := (derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) e₀ inferInstance).ofNatIsoLeft
      (canonicalEtaleCompactSupportComparison A e₀ c₀).symm
  have hc : etaleNormalizedSupportExchange A sq₀ c c₀ =
      EtaleSupportExchange.exchangeIso A c w := by
    unfold etaleNormalizedSupportExchange EtaleSupportExchange.exchangeIso
    rw [(unboundedEtaleCompactSupport_comparison_coherence A e₀).1]
    ext M
    simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Iso.refl_hom, NatTrans.id_app]
    erw [Category.comp_id]
  have hw := NatTrans.congr_app
    (EtaleSupportExchange.rightMate_eq A e c w G G₀ adj adj₀) K
  have hw' : (etaleNormalizedRightExchange A sq₀ c c₀ G G₀ adj adj₀).app K ≫
      (EtaleSupportExchange.rightAdjointIso A e₀ c₀ G₀ adj₀).hom.app
        ((upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.obj K) =
      (upperStar (ModuleCat.{u + 1} A) w₀).mapDerivedCategory.map
        ((EtaleSupportExchange.rightAdjointIso A e c G adj).hom.app K) ≫
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq₀.toCommSq).inv.app K := by
    unfold etaleNormalizedRightExchange
    rw [hc]
    exact hw
  let q := sq.flip.isoPullback.hom
  have sq₂ : IsPullback q e' e₀ (𝟙 X') :=
    IsPullback.of_horiz_isIso ⟨by
      simpa only [q, e₀, Category.comp_id] using sq.flip.isoPullback_hom_fst⟩
  have sq₃ : IsPullback (q ≫ w₀) e' e (𝟙 X' ≫ w) := by
    simpa only [q, w₀, sq.flip.isoPullback_hom_snd, Category.id_comp] using sq
  have hz := etaleNormalizedMates_openRestriction A sq₂ c₀ d G₀ G' adj₀ adj'
    ((upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.obj K)
  have hp := etaleNormalizedMates_normalization_pasting A sq₀ sq₂ sq₃ c c₀ d
    G G₀ G' adj adj₀ adj' K hw' hz
  have hq : q ≫ pullback.snd w e = w' := sq.flip.isoPullback_hom_snd
  let P (a : U' ⟶ U) (b : X' ⟶ X) : Prop :=
    ∀ s : IsPullback a e' e b,
      (etaleNormalizedRightExchange A s c d G G' adj adj').app K ≫
        (EtaleSupportExchange.rightAdjointIso A e' d G' adj').hom.app
          ((upperStar (ModuleCat.{u + 1} A) b).mapDerivedCategory.obj K) =
      (upperStar (ModuleCat.{u + 1} A) a).mapDerivedCategory.map
        ((EtaleSupportExchange.rightAdjointIso A e c G adj).hom.app K) ≫
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) s.toCommSq).inv.app K
  have hp' : P (q ≫ pullback.snd w e) (𝟙 X' ≫ w) := fun _ ↦ hp
  rw [hq, Category.id_comp] at hp'
  exact hp' sq

private lemma mate_ofNatIsoLeft
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : L₁ ≅ L₁') (e' : L₂ ≅ L₂')
    (α : TwoSquare G L₁' L₂' H) :
    (mateEquiv (a.ofNatIsoLeft e) (b.ofNatIsoLeft e') α) =
      (mateEquiv a b ((α.whiskerRight e'.hom).whiskerLeft e.inv)) := by
  ext K
  simp [mateEquiv_apply, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoLeft_counit, Category.assoc, ← Functor.map_comp]

private lemma conjugate_left_transport
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (e : L ≅ L') :
    (conjugateIsoEquiv (a.ofNatIsoLeft e) a e).hom = 𝟙 R := by
  ext K
  apply (a.homEquiv _ _).symm.injective
  change L.map ((conjugateEquiv (a.ofNatIsoLeft e) a e.hom).app K) ≫
      a.counit.app K = _
  rw [conjugateEquiv_counit]
  simp [Adjunction.ofNatIsoLeft_counit, Adjunction.homEquiv_counit]

private theorem normalized_exact_inverse
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {r : X' ⟶ X} {r₁ : U' ⟶ U}
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e']
    [QuasiCompact e] [QuasiCompact e']
    (sq : IsPullback r₁ e' e r) (c : Compactification e) (d : Compactification e')
    (M : DerivedCategoryModule A U) :
    (N.comparison e' d).inv.app
        ((upperStar (ModuleCat.{u + 1} A) r₁).mapDerivedCategory.obj M) ≫
      (etaleNormalizedSupportExchange A sq c d).inv.app M ≫
      (upperStar (ModuleCat.{u + 1} A) r).mapDerivedCategory.map
        ((N.comparison e c).hom.app M) =
      (((mateEquiv
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e'
          inferInstance)).symm
        (TwoSquare.mk _ _ _ _
          (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).inv)
        ).app M) := by
  rw [normalization_comparison_eq_canonical A N e c,
    normalization_comparison_eq_canonical A N e' d]
  let a := derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) e inferInstance
  let b := derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) e' inferInstance
  let dc := canonicalEtaleCompactSupportComparison A e c
  let dd := canonicalEtaleCompactSupportComparison A e' d
  let α := TwoSquare.mk _ _ _ _ (etaleNormalizedSupportExchange A sq c d).inv
  have h := normalized_square A sq c d _ _
    (a.ofNatIsoLeft dc.symm) (b.ofNatIsoLeft dd.symm)
  have hm := mate_ofNatIsoLeft a b dc.symm dd.symm α
  simp only [Iso.symm_hom, Iso.symm_inv] at hm
  have he : mateEquiv a b ((α.whiskerRight dd.inv).whiskerLeft dc.hom) =
      TwoSquare.mk _ _ _ _
        (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).inv := by
    ext K
    rw [← hm]
    have hK := h K
    change (mateEquiv (a.ofNatIsoLeft dc.symm) (b.ofNatIsoLeft dd.symm) α
      ).app K ≫
        (conjugateIsoEquiv (b.ofNatIsoLeft dd.symm) b dd.symm).hom.app _ =
      (upperStar (ModuleCat.{u + 1} A) r₁).mapDerivedCategory.map
        ((conjugateIsoEquiv (a.ofNatIsoLeft dc.symm) a dc.symm).hom.app K) ≫ _ at hK
    dsimp only [a, b, dc, dd, α] at hK ⊢
    simp only [conjugate_left_transport, NatTrans.id_app,
      CategoryTheory.Functor.map_id, Category.id_comp] at hK
    erw [Category.comp_id] at hK
    exact hK
  have he' := (mateEquiv a b).symm_apply_eq.mpr he.symm
  have hh := congrArg (fun t ↦ t.app M) he'
  simpa only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app,
    α, dc, dd, Category.assoc] using hh.symm

private theorem inverseMate_ofNatIsoRight
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (a : L ⊣ R) (b : L' ⊣ R')
    {S : D ⥤ C} {S' : F ⥤ E} (e : S ≅ R) (f : S' ≅ R')
    (β : TwoSquare R H G R') :
    ((mateEquiv (a.ofNatIsoRight e.symm) (b.ofNatIsoRight f.symm)).symm
      (TwoSquare.mk _ _ _ _
        (Functor.whiskerRight e.hom G ≫ β ≫
          Functor.whiskerLeft H f.inv))) =
      ((mateEquiv a b).symm β) := by
  ext X
  dsimp only [mateEquiv, Equiv.coe_fn_symm_mk, Adjunction.ofNatIsoRight_unit,
    Adjunction.ofNatIsoRight_counit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_obj, Functor.comp_map,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoRight_counit,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.comp_id]

private theorem inverseMate_edges
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    {G G' : C ⥤ E} {H H' : D ⥤ F}
    (a : L ⊣ R) (b : L' ⊣ R')
    (β : TwoSquare R H G R') (e : G' ⟶ G) (f : H ⟶ H') :
    (mateEquiv a b).symm ((β.whiskerRight e).whiskerLeft f) =
      (((mateEquiv a b).symm β).whiskerTop e).whiskerBottom f := by
  apply (mateEquiv a b).injective
  rw [Equiv.apply_symm_apply, mateEquiv_whiskerTop_whiskerBottom,
    Equiv.apply_symm_apply]

private theorem leftDerived_square_inverse
    (A : Type (u + 1)) [CommRing A]
    {U U' X X' : Scheme.{u}}
    {e : U ⟶ X} {e' : U' ⟶ X'} {r : X' ⟶ X} {r₁ : U' ⟶ U}
    (sq : CommSq r₁ e' e r) :
    Functor.whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).hom
        (upperStar (ModuleCat.{u + 1} A) r₁).leftDerivedFunctor ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) r₁).hom ≫
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv ≫
      Functor.whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) r).inv
        (upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e').inv =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv := by
  let B := ModuleCat.{u + 1} A
  let α := TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso B sq).hom
  have hs :
      ((((α.whiskerTop (leftDerivedUpperStarIsoMapDerivedCategory B r).hom).whiskerBottom
        (leftDerivedUpperStarIsoMapDerivedCategory B r₁).inv).whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory B e').hom).whiskerLeft
        (leftDerivedUpperStarIsoMapDerivedCategory B e).inv) =
      TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso B sq).hom := by
    ext M
    simp only [α, TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
      TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.mk]
    simp only [derivedSquareUpperStarIso, leftDerivedUpperStarComp,
      exactDerivedSquareUpperStarIso, squareUpperStarIso,
      Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
      leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Category.assoc,
      Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
      Iso.inv_hom_id_app_assoc]
    rw [← (upperStar B r₁).leftDerivedFunctorIsoMapDerivedCategory.inv.naturality]
  let q := ((((α.whiskerTop
    (leftDerivedUpperStarIsoMapDerivedCategory B r).hom).whiskerBottom
      (leftDerivedUpperStarIsoMapDerivedCategory B r₁).inv).whiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory B e').hom).whiskerLeft
      (leftDerivedUpperStarIsoMapDerivedCategory B e).inv)
  have : IsIso q := by
    dsimp only [q, α, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.mk]
    infer_instance
  have hq : asIso q = derivedSquareUpperStarIso B sq :=
    Iso.ext (hs)
  have hi := congrArg Iso.inv hq
  simpa only [q, TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.mk, IsIso.inv_comp,
    Functor.inv_whiskerLeft, Functor.inv_whiskerRight, asIso_inv,
    IsIso.Iso.inv_inv, IsIso.Iso.inv_hom, B, α, Category.assoc] using hi

private theorem leftDerived_sum_mate
    (A : Type (u + 1)) [CommRing A]
    {U U' X X' : Scheme.{u}}
    {e : U ⟶ X} {e' : U' ⟶ X'} {r : X' ⟶ X} {r₁ : U' ⟶ U}
    [Etale e] [Etale e'] (sq : CommSq r₁ e' e r) :
    Functor.whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) r₁).hom
        (etaleLowerShriek (ModuleCat.{u + 1} A) e' inferInstance).mapDerivedCategory ≫
      (((mateEquiv
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e'
          inferInstance)).symm
        (TwoSquare.mk _ _ _ _
          (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv))) ≫
      Functor.whiskerLeft
        (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) r).inv =
      (((mateEquiv
        ((derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) e inferInstance).ofNatIsoRight
            (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).symm)
        ((derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) e' inferInstance).ofNatIsoRight
            (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e').symm)).symm
        (TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso
          (ModuleCat.{u + 1} A) sq).inv))) := by
  let a := derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) e inferInstance
  let b := derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) e' inferInstance
  let β := TwoSquare.mk _ _ _ _
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv
  let t := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) r₁).hom
  let z := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) r).inv
  have h₁ := (inverseMate_edges a b β t z)
  have h₂ := inverseMate_ofNatIsoRight a b
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e')
    ((β.whiskerRight t).whiskerLeft z)
  rw [show Functor.whiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).hom _ ≫
      ((β.whiskerRight t).whiskerLeft z) ≫
      Functor.whiskerLeft _
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e').inv =
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv by
    simpa only [β, t, z, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
      TwoSquare.mk, Category.assoc] using
      leftDerived_square_inverse A sq] at h₂
  simpa only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.mk,
    a, b, β, t, z, Category.assoc] using h₁.symm.trans h₂.symm

private theorem chosen_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {w : X' ⟶ X} {w' : U' ⟶ U}
    [Etale e] [IsSeparated e] [QuasiCompact e] [QuasiCompact e']
    [HasCompactification e] [HasCompactification e'] (sq : IsPullback w' e' e w) :
    unboundedEtaleCompactSupportBaseChange A sq =
      (etaleNormalizedSupportExchange A sq (HasCompactification.compactification e)
        (HasCompactification.compactification e')).hom := by
  have h := (unboundedEtaleCompactSupport_baseChange A sq).2
    (HasCompactification.compactification e)
  rw [rightDerivedLowerShriekIso,
    (unboundedEtaleCompactSupport_comparison_coherence A e).1] at h
  ext M
  have hh := NatTrans.congr_app h M
  simp only [Iso.refl_inv, unboundedEtaleCompactSupportExchange,
    etaleNormalizedSupportExchange, rightDerivedLowerShriekIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, asIso_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app, Category.assoc,
    rightDerivedLowerShriek] at hh ⊢
  have hid := (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.map_id
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (HasCompactification.compactification e)).obj M)
  erw [hid, Category.id_comp] at hh
  exact hh

set_option maxRecDepth 2048 in
private theorem leftDerived_composition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' B B' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    [IsNoetherian B] [IsNoetherian B']
    {e : U ⟶ X} {e' : U' ⟶ X'} {f : X ⟶ B} {f' : X' ⟶ B'}
    {r₁ : U' ⟶ U} {r : X' ⟶ X} {v : B' ⟶ B}
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [QuasiCompact e'] [QuasiCompact f'] [QuasiCompact (e' ≫ f')]
    [HasCompactification e] [HasCompactification f] [HasCompactification (e ≫ f)]
    [HasCompactification e'] [HasCompactification f'] [HasCompactification (e' ≫ f')]
    (sqe : IsPullback r₁ e' e r) (sqf : IsPullback r f' f v)
    (sqef : IsPullback r₁ (e' ≫ f') (e ≫ f) v) (M : DerivedCategoryModule A U) :
    (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.map
        ((unboundedEtaleLowerShriekCompIso A e f).hom.app M) ≫
      (rightDerivedLowerShriekBaseChangeMap A sqef).app M =
      (rightDerivedLowerShriekBaseChangeMap A sqf).app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) e).obj M) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f').map
        ((rightDerivedLowerShriekBaseChangeMap A sqe).app M) ≫
      (unboundedEtaleLowerShriekCompIso A e' f').hom.app
        ((upperStar (ModuleCat.{u + 1} A) r₁).leftDerivedFunctor.obj M) := by
  have h := NatTrans.congr_app
    (unboundedEtaleCompactSupport_baseChange_composition A sqe sqf sqef) M
  simp only [unboundedEtaleCompactSupportBaseChange, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_obj, Category.id_comp,
    Functor.map_comp, Category.assoc] at h
  rw [(leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) v).inv.naturality_assoc] at h
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] at h
  have hn := (unboundedEtaleLowerShriekCompIso A e' f').hom.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) r₁).hom.app M)
  dsimp only [Functor.comp_map] at hn
  rw [hn] at h
  apply (cancel_epi ((leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) v).inv.app
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) e).obj M)))).mp
  apply (cancel_mono ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e' ≫ f')).map
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) r₁).hom.app M))).mp
  simpa only [Category.assoc] using h

private theorem normalized_leftDerived_inverse
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {r : X' ⟶ X} {r₁ : U' ⟶ U}
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e']
    [QuasiCompact e] [QuasiCompact e']
    [HasCompactification e] [HasCompactification e']
    (sq : IsPullback r₁ e' e r) (M : DerivedCategoryModule A U) :
    letI := isIso_rightDerivedLowerShriekBaseChangeMap A sq
    (inv (rightDerivedLowerShriekBaseChangeMap A sq)).app M ≫
      (upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.map
        ((N.comparison e (HasCompactification.compactification e)).hom.app M) =
      (N.comparison e' (HasCompactification.compactification e')).hom.app
        ((upperStar (ModuleCat.{u + 1} A) r₁).leftDerivedFunctor.obj M) ≫
      (((mateEquiv
        ((derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) e inferInstance).ofNatIsoRight
            (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).symm)
        ((derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) e' inferInstance).ofNatIsoRight
            (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e').symm)).symm
        (TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso
          (ModuleCat.{u + 1} A) sq.toCommSq).inv)).app M) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  have := (unboundedEtaleCompactSupport_baseChange A sq).1
  let c := HasCompactification.compactification e
  let d := HasCompactification.compactification e'
  let dc := N.comparison e c
  let dd := N.comparison e' d
  let E' := (etaleLowerShriek (ModuleCat.{u + 1} A) e' inferInstance).mapDerivedCategory
  let pr := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) r
  let pr₁ := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) r₁
  have hx : (etaleNormalizedSupportExchange A sq c d).inv =
      Functor.whiskerRight pr₁.inv (rightDerivedLowerShriek (ModuleCat.{u + 1} A) e') ≫
      inv (rightDerivedLowerShriekBaseChangeMap A sq) ≫
      Functor.whiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) e) pr.hom := by
    have hi : etaleNormalizedSupportExchange A sq c d =
        asIso (unboundedEtaleCompactSupportBaseChange A sq) :=
      Iso.ext (chosen_exchange A sq).symm
    rw [hi]
    simp only [unboundedEtaleCompactSupportBaseChange, IsIso.inv_comp,
      Functor.inv_whiskerLeft, Functor.inv_whiskerRight, asIso_inv, IsIso.Iso.inv_inv,
      IsIso.Iso.inv_hom, pr, pr₁, Category.assoc]
  have h := normalized_exact_inverse A N sq c d M
  rw [hx] at h
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc] at h
  dsimp only [rightDerivedLowerShriek] at h
  rw [← (N.comparison e' d).inv.naturality_assoc, ← pr.hom.naturality] at h
  have hh := congrArg (fun k ↦ E'.map (pr₁.hom.app M) ≫ k ≫
    pr.inv.app ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance
      ).mapDerivedCategory.obj M)) h
  dsimp only [E'] at hh
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] at hh
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at hh
  have ht := NatTrans.congr_app (leftDerived_sum_mate A sq.toCommSq) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at ht
  have he := hh.trans ht
  apply (cancel_epi (dd.inv.app
    ((upperStar (ModuleCat.{u + 1} A) r₁).leftDerivedFunctor.obj M))).mp
  simpa only [← Category.assoc, dd, d, c, Iso.inv_hom_id_app,
    Category.id_comp] using he

/-- Inverse compact-support exchange preserves the etale composition comparison.
Source: Stacks Project, Tags 0F7J and 0F7L, together with Tag 03S6
(blueprint: lem-amb-etale-left-comparison-base-change).

Proof: write the etale left comparison as the graph-normalized comparison from sum
extension to the compact-support candidate, followed by the compact-support composition
map and independence of compactification. The composition/base-change equation of
`unboundedEtaleCompactSupport_baseChange_composition` identifies the two ways to move
compact-support exchange through this composite. The graph-normalization base-change
identity identifies the remaining exchange for the etale factor with inverse sum exchange.
To identify this inverse sum exchange with the displayed inverse mate, transpose under
sum extension/restriction on both sides. Its definition as the conjugate of ordinary
inverse-image/direct-image exchange, naturality, and the two adjunction triangle identities
give exactly the canonical inverse-image square. This calculation holds on sheaves, descends
termwise to complexes, and then to the whole unbounded derived categories. Transport exact
inverse image to its canonical left-derived realization. Cancel the invertible composition
comparisons and exchanges; the resulting component equation is the displayed one.

More explicitly, refinement normalization and `N.refinement` imply
`I(d,c).hom ≫ (N.comparison u c).hom = (N.comparison u d).hom` for a proper
refinement from `c` to `d`. A common refinement and the comparison cocycle give this
identity for any two compactifications. Hence the etale left comparison can be computed
using the chosen compactification of `u`, with its graph comparison inserted before the
canonical compact-support compositor. The compositor/exchange equation then gives
`xi_uf ≫ v*(alpha.inv) = alpha'.inv ≫ F'(xi_u) ≫ xi_f(E(-))`, initially with
`xi_u` the inverse sum-exchange map. An arbitrary Cartesian square is transported to the
chosen fibre product by its unique pullback isomorphism; the inverse-image compositors
supply exactly the `J` in the statement.

To check the remaining identification of `xi_u`, let `ev` denote the sum-extension
counit. The mate counit equation to prove is
`E'(J_M) ≫ ev' = xi_u(u*M) ≫ r*(ev_M)`.
On sheaves, transpose both sides under the composite adjunction of sum extension with
inverse image. By the defining conjugate formula, the transpose of the right side is
ordinary exchange followed by the composite unit and pulled-back evaluation. Naturality
of ordinary exchange and `u*(ev) ≫ unit = id` reduce it to ordinary exchange followed
by the inverse-image unit. Expand ordinary exchange as the transpose of the commuting
inverse-image square. Naturality of that square and the inverse-image triangle identity
reduce the result to `r1_*(J_M) ≫ unit_r1`. Transposing the left side gives the same
map by the sum-extension triangle identity. Thus the adjunction bijection proves the
counit equation. Exactness and termwise derivation preserve this equation; injectivity
of the mates correspondence identifies this `xi_u` with the inverse mate displayed below.
No smoothness, section, fibre parameter, or dualizing complex enters this calculation. -/
theorem etaleAmbientLeftComparison_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U X B U' X' B' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian B]
    [IsNoetherian U'] [IsNoetherian X'] [IsNoetherian B']
    (u : U ⟶ X) (f : X ⟶ B) (u' : U' ⟶ X') (f' : X' ⟶ B')
    [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    [Etale u'] [IsSeparated u'] [LocallyOfFiniteType u'] [QuasiCompact u']
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f']
    [HasCompactification (u ≫ f)] [HasCompactification (u' ≫ f')]
    [QuasiCompact f'] [QuasiCompact (u' ≫ f')]
    (v : B' ⟶ B) (r : X' ⟶ X) (r₁ : U' ⟶ U)
    (sq : IsPullback r f' f v) (sqU : IsPullback r₁ u' u r)
    (sq₁ : IsPullback r₁ (u' ≫ f') (u ≫ f) v)
    (M : DerivedCategoryModule A U) :
    letI := isIso_rightDerivedLowerShriekBaseChangeMap A sq
    letI := isIso_rightDerivedLowerShriekBaseChangeMap A sq₁
    (inv (rightDerivedLowerShriekBaseChangeMap A sq₁)).app M ≫
        (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.map
          ((etaleAmbientLeftComparison A N u f
            (HasCompactification.compactification f)
            (HasCompactification.compactification (u ≫ f))).inv.app M) =
      (etaleAmbientLeftComparison A N u' f'
        (HasCompactification.compactification f')
        (HasCompactification.compactification (u' ≫ f'))).inv.app
          ((upperStar (ModuleCat.{u + 1} A) r₁).leftDerivedFunctor.obj M) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f').map
        (((mateEquiv
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) u inferInstance).ofNatIsoRight
              (leftDerivedUpperStarIsoMapDerivedCategory
                (ModuleCat.{u + 1} A) u).symm)
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) u' inferInstance).ofNatIsoRight
              (leftDerivedUpperStarIsoMapDerivedCategory
                (ModuleCat.{u + 1} A) u').symm)).symm
          (TwoSquare.mk _ _ _ _
            (((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r₁ u).symm ≪≫
              leftDerivedUpperStarComp (ModuleCat.{u + 1} A) u' r (r₁ ≫ u)
                sqU.w).hom))).app M) ≫
      (inv (rightDerivedLowerShriekBaseChangeMap A sq)).app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance).mapDerivedCategory.obj M) := by
  let : HasCompactification u :=
    (((HasCompactification.compactification (u ≫ f)).ofComp
      (HasCompactification.compactification f)).restrict).hasCompactification
  let : HasCompactification u' :=
    (((HasCompactification.compactification (u' ≫ f')).ofComp
      (HasCompactification.compactification f')).restrict).hasCompactification
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sqU
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq₁
  let t := unboundedEtaleLowerShriekCompIso A u f
  let t' := unboundedEtaleLowerShriekCompIso A u' f'
  let V := (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor
  let F' := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'
  let C := rightDerivedLowerShriekBaseChangeMap A sq
  let Cu := rightDerivedLowerShriekBaseChangeMap A sqU
  let C₁ := rightDerivedLowerShriekBaseChangeMap A sq₁
  have hc := leftDerived_composition A sqU sq sq₁ M
  have hi : asIso (V.map (t.hom.app M)) ≪≫ asIso (C₁.app M) =
      asIso (C.app ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) u).obj M)) ≪≫
        asIso (F'.map (Cu.app M)) ≪≫
        asIso (t'.hom.app
          ((upperStar (ModuleCat.{u + 1} A) r₁).leftDerivedFunctor.obj M)) :=
    Iso.ext hc
  have hinv := congrArg Iso.inv hi
  simp only [Iso.trans_inv, asIso_inv, ← Functor.map_inv,
    ← NatIso.isIso_inv_app, IsIso.Iso.inv_hom, Category.assoc] at hinv
  rw [left_comparison_chosen A N u f, left_comparison_chosen A N u' f']
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  dsimp only [rightDerivedLowerShriek] at hinv ⊢
  rw [← Category.assoc, hinv]
  simp only [Category.assoc]
  have hn := (inv C).naturality
    ((N.comparison u (HasCompactification.compactification u)).hom.app M)
  change F'.map ((upperStar (ModuleCat.{u + 1} A) r).leftDerivedFunctor.map
      ((N.comparison u (HasCompactification.compactification u)).hom.app M)) ≫
        (inv C).app
          ((etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance
            ).mapDerivedCategory.obj M) =
    (inv C).app ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) u).obj M) ≫
      V.map ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        ((N.comparison u (HasCompactification.compactification u)).hom.app M)) at hn
  erw [← hn]
  have hu := normalized_leftDerived_inverse A N sqU M
  have hF := congrArg (fun k ↦ F'.map k) hu
  have h := congrArg (fun k ↦
    t'.inv.app ((upperStar (ModuleCat.{u + 1} A) r₁).leftDerivedFunctor.obj M) ≫ k ≫
      (inv C).app ((etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance
        ).mapDerivedCategory.obj M)) hF
  simpa only [Functor.map_comp, Functor.comp_obj, Category.assoc,
    derivedSquareUpperStarIso, Iso.trans_inv, Iso.symm_inv, Iso.trans_hom,
    Iso.symm_hom, t', F', C, Cu, rightDerivedLowerShriek] using h

end AlgebraicGeometry.Etale
