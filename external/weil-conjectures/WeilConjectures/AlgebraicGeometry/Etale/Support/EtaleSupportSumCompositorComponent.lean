/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumCompositionCounit

import WeilConjectures.AlgebraicGeometry.QuasiFinite.QuasiFiniteCompactSupportExact
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFiniteCompactificationSheafIso
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationSheafRefinement
import WeilConjectures.AlgebraicGeometry.Exact.ExactCompactificationUnitRefinement
import WeilConjectures.AlgebraicGeometry.Exact.ExactCompactificationUnitTower
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphismComparison
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization

/-! Component form of the support/sum compositor equation.

Source: Stacks Project, More on Etale Cohomology, Tags 0F7J, 0F7K and 0F50.
(blueprint: lem-pur-etale-support-sum-compositor-component).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private lemma graph_sheaf_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (f : U ⟶ X) [Etale f] [IsSeparated f] [QuasiCompact f]
    (c : Compactification f) : IsIso (etaleCompactificationGraphMap A f c) := by
  classical
  obtain ⟨L, ι, _, hp, ho, σ, _, hσ, _, _⟩ := properSupportSheafComposition A
  have hproper {V W : Scheme.{u}} (g : V ⟶ W) [IsProper g] : IsIso (ι g) := by
    have : ∀ M, IsIso ((ι g).app M) := hp V W g
    exact NatIso.isIso_of_isIso_app _
  have hfac {V W : Scheme.{u}} (g : V ⟶ W) [IsSeparated g]
      [LocallyOfFiniteType g] (d : Compactification g) :
      ∃ α : openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i ⋙
          lowerStar (ModuleCat.{u + 1} A) d.g ≅ L g,
        α.hom ≫ ι g = compactificationSheafToDirectImage A d := by
    rcases d with ⟨Z, p, j, rfl, hpp, hj⟩
    have := hpp
    have := hj
    obtain ⟨oj, hoj⟩ := ho V Z j
    have := hproper p
    let α := Functor.isoWhiskerRight oj (lowerStar (ModuleCat.{u + 1} A) p) ≪≫
      Functor.isoWhiskerLeft (L j) (asIso (ι p)).symm ≪≫ σ V Z W j p
    refine ⟨α, ?_⟩
    apply NatTrans.ext
    funext M
    dsimp only [α, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatTrans.comp_app]
    rw [Category.assoc, Category.assoc, hσ]
    have hcancel : (asIso (ι p)).inv.app ((L j).obj M) ≫
        (ι p).app ((L j).obj M) = 𝟙 _ := (asIso (ι p)).inv_hom_id_app _
    rw [reassoc_of% hcancel, ← Functor.map_comp_assoc]
    change (lowerStar (ModuleCat.{u + 1} A) p).map
      ((oj.hom ≫ ι j).app M) ≫ _ = _
    rw [hoj]
    rfl
  obtain ⟨Z, j, p, hj, _, hpf, hcomm⟩ :=
    f.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
  have := hj
  have := hpf
  let d : Compactification f := ⟨Z, p, j, hcomm.symm, inferInstance, hj⟩
  have := isIso_etaleCompactificationGraphMap_of_isFinite A f d
  obtain ⟨α, hα⟩ := hfac f d
  let o := asIso (etaleCompactificationGraphMap A f d) ≪≫ α
  have hon (M) : o.hom.app M ≫ (ι f).app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f M := by
    simp only [o, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
    change (etaleCompactificationGraphMap A f d).app M ≫
      (α.hom.app M ≫ (ι f).app M) = _
    rw [← NatTrans.comp_app, hα]
    exact compactSupportGraphSheafComparison_normalization A f d M
  obtain ⟨β, hβ⟩ := hfac f c
  have hm := (compactificationSheafRefinement_properties A
    (Compactification.Refinement.id c) IsPullback.of_id_snd).2
  have : ∀ M, Mono ((compactificationSheafToDirectImage A c).app M) := hm
  have heq : etaleCompactificationGraphMap A f c = (o ≪≫ β.symm).hom := by
    apply NatTrans.ext
    funext M
    apply (cancel_mono ((compactificationSheafToDirectImage A c).app M)).1
    rw [compactSupportGraphSheafComparison_normalization]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
    have hh := congr_app hβ M
    simp only [NatTrans.comp_app] at hh
    rw [← hh, Iso.inv_hom_id_app_assoc, hon]
  rw [heq]
  infer_instance

set_option maxRecDepth 4096 in
private lemma sum_sheaf_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X T : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian T]
    (e : U ⟶ X) (v : X ⟶ T)
    [Etale e] [Etale v] [IsSeparated e] [IsSeparated v]
    [QuasiCompact e] [QuasiCompact v]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleSumSheafCompIso A e v).hom.app M ≫
        etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) (e ≫ v) M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) v
          ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M) ≫
        (lowerStar (ModuleCat.{u + 1} A) v).map
          (etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) e M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) e v).hom.app M := by
  obtain ⟨L, ι, o, hA, hL, hC, eA, eL, eC, heA, heL, heC,
    ch, ce, che, idA, idL, idC, cid, props⟩ :=
    quasifiniteCompactSupportExact A e v
      ((Scheme.Hom.isQuasiFinite_iff e).2 ⟨inferInstance, inferInstance, inferInstance⟩)
      ((Scheme.Hom.isQuasiFinite_iff v).2 ⟨inferInstance, inferInstance, inferInstance⟩)
  obtain ⟨_, _, _, _, _, _, _, _, ⟨σ, nσ, _, hsum⟩, ho, _⟩ := props
  let Se := etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance
  let Sv := etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance
  have ht : (etaleSumSheafCompIso A e v).hom.app M ≫ (o (e ≫ v)).hom.app M =
      Sv.map ((o e).hom.app M) ≫ (o v).hom.app ((L e).obj M) ≫ σ.hom.app M := by
    apply (((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) e).comp
      (etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) v)).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    have hh := hsum M W.unop
    have hs := etaleSumSheafCompIso_summand A e v M W.unop
    have hn := (o (e ≫ v)).hom.app M |>.hom.naturality
      ((MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale e)
        (inferInstance : Etale v)).inv.app W.unop).op
    let We : X.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W.unop
    let Wev : T.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale v)).obj We
    change ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) e).unit.app M).hom.app
          W ≫
        ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) v).unit.app
          (Se.obj M)).hom.app (Opposite.op We) ≫
        ((etaleSumSheafCompIso A e v).hom.app M).hom.app (Opposite.op Wev) ≫
        ((o (e ≫ v)).hom.app M).hom.app (Opposite.op Wev) =
      ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) e).unit.app M).hom.app W ≫
        ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) v).unit.app
          (Se.obj M)).hom.app (Opposite.op We) ≫
        (Sv.map ((o e).hom.app M)).hom.app (Opposite.op Wev) ≫
        ((o v).hom.app ((L e).obj M)).hom.app (Opposite.op Wev) ≫
        (σ.hom.app M).hom.app (Opposite.op Wev)
    have hu := (etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) v).unit.naturality
      ((o e).hom.app M)
    have huu := congrArg (fun t ↦ t.hom.app (Opposite.op We)) hu
    change ((o e).hom.app M).hom.app (Opposite.op We) ≫
        ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) v).unit.app
          ((L e).obj M)).hom.app (Opposite.op We) =
      ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) v).unit.app
          (Se.obj M)).hom.app (Opposite.op We) ≫
        (Sv.map ((o e).hom.app M)).hom.app (Opposite.op Wev) at huu
    rw [← reassoc_of% huu, hh, reassoc_of% hs]
    exact congrArg
      (((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A)
        (e ≫ v)).unit.app M).hom.app W ≫ ·) hn
  rw [← ho U T (e ≫ v) M, ← Category.assoc, ht]
  simp only [Category.assoc]
  rw [nσ]
  rw [(o v).hom.naturality_assoc, (ι v).naturality_assoc]
  rw [reassoc_of% ho X T v (Se.obj M), ← Functor.map_comp_assoc, ho U X e]

private lemma graph_unit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f] [QuasiCompact f]
    (c : Compactification f)
    (a : etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (ha : a.hom = etaleCompactificationGraphMap A f c) :
    exactCompactificationUnit A c _ a =
      (canonicalEtaleCompactSupportComparison A f c).inv := by
  change exactCompactificationUnit A c _ a =
    compactSupportDerivedComparison A f c (etaleCompactificationGraphMap A f c)
  unfold exactCompactificationUnit compactSupportDerivedComparison
  rw [ha]
  rfl

private lemma unit_naturality
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (F H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (σ : F ≅ H)
    (a : H ≅ openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
      lowerStar (ModuleCat.{u + 1} A) c.g) :
    exactCompactificationUnit A c F (σ ≪≫ a) =
      (Functor.mapDerivedCategoryNatIso σ).hom ≫ exactCompactificationUnit A c H a := by
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (.up ℤ))
  intro K
  simp only [NatTrans.comp_app]
  unfold exactCompactificationUnit
  rw [normalizationLocalizationDesc_app, normalizationLocalizationDesc_app]
  simp only [Iso.trans_hom, NatTrans.mapHomotopyCategory_comp,
    Functor.whiskerRight_comp, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_fach σ K)]

/-- The support/sum compositor equation at one derived-category object.
Source: Stacks Project, Tags 0F7J, 0F7K and 0F50.
(blueprint: lem-pur-etale-support-sum-compositor-component).

The component equation is obtained by the graph-normalized exact support construction,
the nested-summand calculation, and exact compactification-unit composition. It is the
objectwise form of the natural-transformation equation used by the compositor. -/
theorem etaleSupportSumCompositor_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X T : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian T]
    (e : U ⟶ X) (v : X ⟶ T)
    [Etale e] [Etale v] [IsSeparated e] [IsSeparated v]
    [QuasiCompact e] [QuasiCompact v]
    (c : Compactification e) (d : Compactification v) (k : Compactification (e ≫ v))
    (M : DerivedCategoryModule A U) :
    ((Functor.isoWhiskerRight
        (rightDerivedLowerShriekOfCompactificationIso A c (k.ofComp d).restrict) _ ≪≫
      rightDerivedLowerShriekOfCompactificationCompIso A d (k.ofComp d) ≪≫
      rightDerivedLowerShriekOfCompactificationIso A (d.comp (k.ofComp d)) k).hom.app M ≫
        (canonicalEtaleCompactSupportComparison A (e ≫ v) k).hom.app M) =
      (NatTrans.hcomp (canonicalEtaleCompactSupportComparison A e c).hom
          (canonicalEtaleCompactSupportComparison A v d).hom ≫
        (derivedEtaleSumCompIso A e v).hom).app M := by
  let c' := k.ofComp d
  let Se := etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance
  let Sv := etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance
  let Sev := etaleLowerShriek (ModuleCat.{u + 1} A) (e ≫ v) inferInstance
  have : IsIso (etaleCompactificationGraphMap A e c) := graph_sheaf_isIso A e c
  have : IsIso (etaleCompactificationGraphMap A e c'.restrict) :=
    graph_sheaf_isIso A e c'.restrict
  have : IsIso (etaleCompactificationGraphMap A v d) := graph_sheaf_isIso A v d
  have : IsIso (etaleCompactificationGraphMap A (e ≫ v) (d.comp c')) :=
    graph_sheaf_isIso A (e ≫ v) (d.comp c')
  have : IsIso (etaleCompactificationGraphMap A (e ≫ v) k) :=
    graph_sheaf_isIso A (e ≫ v) k
  let ac := asIso (etaleCompactificationGraphMap A e c)
  let ac' := asIso (etaleCompactificationGraphMap A e c'.restrict)
  let ad := asIso (etaleCompactificationGraphMap A v d)
  let acomp := asIso (etaleCompactificationGraphMap A (e ≫ v) (d.comp c'))
  let ak := asIso (etaleCompactificationGraphMap A (e ≫ v) k)
  have na (N : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      ((etaleSumSheafCompIso A e v) ≪≫ acomp).hom.app N ≫
          (compactificationSheafToDirectImage A (d.comp c')).app N =
        ad.hom.app (Se.obj N) ≫
          (compactificationSheafToDirectImage A d).app (Se.obj N) ≫
          (lowerStar (ModuleCat.{u + 1} A) v).map
            (ac'.hom.app N ≫
              (compactificationSheafToDirectImage A c'.restrict).app N) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) e v).hom.app N := by
    simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc, ac', asIso_hom]
    change (etaleSumSheafCompIso A e v).hom.app N ≫
        ((etaleCompactificationGraphMap A (e ≫ v) (d.comp c')).app N ≫ _) =
      (etaleCompactificationGraphMap A v d).app (Se.obj N) ≫ _
    rw [compactSupportGraphSheafComparison_normalization,
      reassoc_of% compactSupportGraphSheafComparison_normalization A v d,
      compactSupportGraphSheafComparison_normalization]
    exact sum_sheaf_normalization A e v N
  have ht := exactCompactificationUnit_tower A e v d c' Se Sv ac' ad
    (etaleSumSheafCompIso A e v ≪≫ acomp) na
  rw [unit_naturality] at ht
  rw [graph_unit A e c'.restrict ac' rfl, graph_unit A v d ad rfl,
    graph_unit A (e ≫ v) (d.comp c') acomp rfl] at ht
  have hr := exactCompactificationUnit_refinement A e Se c c'.restrict ac ac' (by
    apply NatTrans.ext
    funext N
    exact (compactSupportGraphSheafComparison_normalization A e c N).trans
      (compactSupportGraphSheafComparison_normalization A e c'.restrict N).symm)
  rw [graph_unit A e c ac rfl, graph_unit A e c'.restrict ac' rfl] at hr
  have hk := exactCompactificationUnit_refinement A (e ≫ v) Sev (d.comp c') k acomp ak (by
    apply NatTrans.ext
    funext N
    exact (compactSupportGraphSheafComparison_normalization A (e ≫ v) (d.comp c') N).trans
      (compactSupportGraphSheafComparison_normalization A (e ≫ v) k N).symm)
  rw [graph_unit A (e ≫ v) (d.comp c') acomp rfl, graph_unit A (e ≫ v) k ak rfl] at hk
  let a := canonicalEtaleCompactSupportComparison A e c
  let b := canonicalEtaleCompactSupportComparison A v d
  let z := canonicalEtaleCompactSupportComparison A (e ≫ v) k
  let t := Functor.isoWhiskerRight
      (rightDerivedLowerShriekOfCompactificationIso A c c'.restrict) _ ≪≫
    rightDerivedLowerShriekOfCompactificationCompIso A d c' ≪≫
    rightDerivedLowerShriekOfCompactificationIso A (d.comp c') k
  have hf : Sv.mapDerivedCategory.map (a.inv.app M) ≫
      b.inv.app ((rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c).obj M) ≫ t.hom.app M =
        (derivedEtaleSumCompIso A e v).hom.app M ≫ z.inv.app M := by
    have htM := congr_app ht M
    have hrM := congr_app hr M
    have hkM := congr_app hk M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] at htM hrM hkM
    simp only [t, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app]
    rw [← b.inv.naturality_assoc, ← Functor.map_comp_assoc, hrM]
    have hpost := congrArg
      (fun q ↦ q ≫
        (rightDerivedLowerShriekOfCompactificationIso A (d.comp c') k).hom.app M) htM
    simpa only [derivedEtaleSumCompIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Category.assoc, hkM] using hpost
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, Category.assoc]
  change t.hom.app M ≫ z.hom.app M =
    b.hom.app _ ≫ Sv.mapDerivedCategory.map (a.hom.app M) ≫
      (derivedEtaleSumCompIso A e v).hom.app M
  apply (cancel_epi (Sv.mapDerivedCategory.map (a.inv.app M) ≫ b.inv.app _)).1
  have hp := congrArg (fun q ↦ q ≫ z.hom.app M) hf
  have hcancel : Sv.mapDerivedCategory.map (a.inv.app M) ≫
      Sv.mapDerivedCategory.map (a.hom.app M) ≫
        (derivedEtaleSumCompIso A e v).hom.app M =
          (derivedEtaleSumCompIso A e v).hom.app M :=
    (Sv.mapDerivedCategory.mapIso (a.app M)).inv_hom_id_assoc _
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
    Category.comp_id, hcancel] using hp

end AlgebraicGeometry.Etale
