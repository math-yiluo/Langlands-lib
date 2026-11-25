/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.QuasiFinite.QuasiFiniteCompactSupportExact
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Basic

import all WeilConjectures.AlgebraicGeometry.EtaleSupportExchange.EtaleSupportExchangeRightMate
import all WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import all WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import all WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekBaseChange
import all WeilConjectures.SixFunctors.Etale.Derived.BaseChangeCube
import all WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphCoherence
import WeilConjectures.AlgebraicGeometry.Etale.Support.EtaleSupportSumCompositor
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleExactSumBaseChangeMate
import WeilConjectures.AlgebraicGeometry.Etale.EtaleExactPullbackSquarePasting

/-! # Composition and pasting of actual normalized etale mates

Source: Stacks Project, More on Etale Cohomology, Tags 0F7J and 0F7K;
Etale Cohomology, Tag 03S6; blueprint etale locality Step 1
(blueprint: lem-pur-etale-normalized-mates-composition-pasting).

All compactifications and all right adjunctions are arbitrary. The support/sum comparison
is the existing constructed graph comparison. The helpers only transport the specified
proper/open compositor and exchange to these fixed compactifications, then take their mates.
No choice of an unrelated natural isomorphism occurs.
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.TwoSquare

namespace AlgebraicGeometry.Etale

attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  canonicalEtaleCompactSupportComparison derivedEtaleLowerShriekUpperStarAdjunction
  rightDerivedLowerShriekOfCompactificationIso unboundedEtaleCompactSupportExchange

/-- The specified proper/open compositor transported to three fixed compactifications.
Source: Stacks Tags 0F7J, 0F7K, 03S6; blueprint etale locality Step 1.
(blueprint: lem-pur-etale-normalized-mates-composition-pasting). -/
noncomputable def etaleNormalizedSupportCompositor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X T : Scheme.{u}} {e : U ⟶ X} {v : X ⟶ T}
    [QuasiCompact e] [QuasiCompact (e ≫ v)]
    (c : Compactification e) (d : Compactification v) (k : Compactification (e ≫ v)) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) k :=
  Functor.isoWhiskerRight
      (rightDerivedLowerShriekOfCompactificationIso A c (k.ofComp d).restrict) _ ≪≫
    rightDerivedLowerShriekOfCompactificationCompIso A d (k.ofComp d) ≪≫
    rightDerivedLowerShriekOfCompactificationIso A (d.comp (k.ofComp d)) k

/-- The actual proper/open exchange, followed by the canonical compactification comparison.
Source: Stacks Tags 0F7J, 0F7K, 03S6; blueprint etale locality Step 1.
(blueprint: lem-pur-etale-normalized-mates-composition-pasting). -/
noncomputable def etaleNormalizedSupportExchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}} {e : U ⟶ X} {e' : U' ⟶ X'}
    {w : X' ⟶ X} {w' : U' ⟶ U} [QuasiCompact e']
    (sq : IsPullback w' e' e w) (c : Compactification e) (d : Compactification e') :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) w').mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d :=
  haveI := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring A
    isAddTorsion_of_finite (IsPullback.of_hasPullback c.g w)
  haveI := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (ModuleCat.{u + 1} A) sq c
  Functor.isoWhiskerLeft
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) w).symm ≪≫
    asIso (rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} A) sq c) ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) w') _ ≪≫
    Functor.isoWhiskerLeft (upperStar (ModuleCat.{u + 1} A) w').mapDerivedCategory
      (rightDerivedLowerShriekOfCompactificationIso A (c.ofIsPullback sq) d)

/-- The right mate B on the entire unbounded category, for arbitrary fixed adjunctions.
Its defining transpose is the inverse support exchange followed by the pulled-back counit.
Source: Stacks Tags 0F7J, 0F7K, 03S6; blueprint etale locality Step 1.
(blueprint: lem-pur-etale-normalized-mates-composition-pasting). -/
noncomputable def etaleNormalizedRightExchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}} {e : U ⟶ X} {e' : U' ⟶ X'}
    {w : X' ⟶ X} {w' : U' ⟶ U} [QuasiCompact e']
    (sq : IsPullback w' e' e w) (c : Compactification e) (d : Compactification e')
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (G' : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ G') :
    G ⋙ (upperStar (ModuleCat.{u + 1} A) w').mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory ⋙ G' :=
  (mateEquiv adj adj' (TwoSquare.mk _ _ _ _
    (etaleNormalizedSupportExchange A sq c d).inv))

private lemma support_exchange_global
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {w : X' ⟶ X} {w' : U' ⟶ U}
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e']
    [QuasiCompact e] [QuasiCompact e']
    (sq : IsPullback w' e' e w) (c : Compactification e) (d : Compactification e')
    (M : DerivedCategoryModule A U) :
    (etaleNormalizedSupportExchange A sq c d).hom.app M ≫
        (rightDerivedLowerShriekIso A d).hom.app
          ((upperStar (ModuleCat.{u + 1} A) w').mapDerivedCategory.obj M) =
      (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.map
          ((rightDerivedLowerShriekIso A c).hom.app M) ≫
        (unboundedEtaleCompactSupportBaseChange A sq).app M := by
  let : HasCompactification e := c.hasCompactification
  let : HasCompactification e' := d.hasCompactification
  have h := NatTrans.congr_app ((unboundedEtaleCompactSupport_baseChange A sq).2 c) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at h
  rw [h, ← Category.assoc, ← Functor.map_comp]
  simp only [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have ht := congrArg (fun t ↦ t.hom.app
      ((upperStar (ModuleCat.{u + 1} A) w').mapDerivedCategory.obj M))
    ((unboundedEtaleCompactSupport_comparison_coherence A e').2
      (c.ofIsPullback sq) d (HasCompactification.compactification e'))
  change _ ≫ (rightDerivedLowerShriekIso A d).hom.app _ = _ at ht
  simpa only [etaleNormalizedSupportExchange, unboundedEtaleCompactSupportExchange,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    asIso_hom, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, rightDerivedLowerShriekIso, Category.assoc] using
      congrArg (fun t ↦ (unboundedEtaleCompactSupportExchange A sq c).app M ≫ t) ht

private lemma support_compositor_global
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X T : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian T]
    (e : U ⟶ X) (v : X ⟶ T)
    [Etale e] [Etale v] [IsSeparated e] [IsSeparated v]
    [QuasiCompact e] [QuasiCompact v]
    (c : Compactification e) (d : Compactification v) (k : Compactification (e ≫ v))
    (M : DerivedCategoryModule A U) :
    (etaleNormalizedSupportCompositor A c d k).hom.app M ≫
        (rightDerivedLowerShriekIso A k).hom.app M =
      (rightDerivedLowerShriekIso A d).hom.app
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) v).map
          ((rightDerivedLowerShriekIso A c).hom.app M) ≫
        (unboundedEtaleLowerShriekCompIso A e v).hom.app M := by
  let : HasCompactification e := c.hasCompactification
  let : HasCompactification v := d.hasCompactification
  let : HasCompactification (e ≫ v) := k.hasCompactification
  let r := (k.ofComp d).restrict
  have ht : (rightDerivedLowerShriekOfCompactificationIso A c r).hom =
      (rightDerivedLowerShriekIso A c).hom ≫ (rightDerivedLowerShriekIso A r).inv := by
    apply (cancel_mono (rightDerivedLowerShriekIso A r).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact congrArg Iso.hom
      ((unboundedEtaleCompactSupport_comparison_coherence A e).2
        c r (HasCompactification.compactification e))
  have hk := congrArg (fun t ↦ t.hom.app M)
    ((unboundedEtaleCompactSupport_comparison_coherence A (e ≫ v)).2
      (d.comp (k.ofComp d)) k (HasCompactification.compactification (e ≫ v)))
  have hg := NatTrans.congr_app (unboundedEtaleLowerShriekCompIso_tower A e v d
    (k.ofComp d)) M
  simp only [NatTrans.comp_app, NatTrans.hcomp_app] at hg
  rw [hg, ← Category.assoc, ← (rightDerivedLowerShriekIso A d).hom.naturality]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  have htM := NatTrans.congr_app ht M
  simp only [NatTrans.comp_app] at htM
  rw [← Functor.map_comp_assoc, ← htM]
  change (rightDerivedLowerShriekOfCompactificationIso A (d.comp (k.ofComp d)) k).hom.app
    M ≫ (rightDerivedLowerShriekIso A k).hom.app M =
      (rightDerivedLowerShriekIso A (d.comp (k.ofComp d))).hom.app M at hk
  simpa only [etaleNormalizedSupportCompositor, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Category.assoc] using congrArg
      (fun t ↦ (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
        ((rightDerivedLowerShriekOfCompactificationIso A c r).hom.app M) ≫
          (rightDerivedLowerShriekOfCompactificationCompIso A d (k.ofComp d)).hom.app M ≫ t)
      hk

private lemma support_exchange_pasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' U'' X X' X'' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian U'']
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    {e : U ⟶ X} {e' : U' ⟶ X'} {e'' : U'' ⟶ X''}
    {w : X' ⟶ X} {z : X'' ⟶ X'} {w' : U' ⟶ U} {z' : U'' ⟶ U'}
    [Etale e] [Etale e'] [Etale e'']
    [IsSeparated e] [IsSeparated e'] [IsSeparated e'']
    [QuasiCompact e] [QuasiCompact e'] [QuasiCompact e'']
    (sq : IsPullback w' e' e w) (sq' : IsPullback z' e'' e' z)
    (sq'' : IsPullback (z' ≫ w') e'' e (z ≫ w))
    (c : Compactification e) (d : Compactification e') (k : Compactification e'')
    (M : DerivedCategoryModule A U) :
    (etaleNormalizedSupportExchange A sq'' c k).hom.app M =
      (unboundedEtaleUpperStarCompIso A z w).hom.app
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ≫
        (upperStar (ModuleCat.{u + 1} A) z).mapDerivedCategory.map
          ((etaleNormalizedSupportExchange A sq c d).hom.app M) ≫
        (etaleNormalizedSupportExchange A sq' d k).hom.app
          ((upperStar (ModuleCat.{u + 1} A) w').mapDerivedCategory.obj M) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) k).map
          ((unboundedEtaleUpperStarCompIso A z' w').inv.app M) := by
  let : HasCompactification e := c.hasCompactification
  let : HasCompactification e' := d.hasCompactification
  let : HasCompactification e'' := k.hasCompactification
  let F₂ := rightDerivedLowerShriek (ModuleCat.{u + 1} A) e''
  let W := (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory
  let Z := (upperStar (ModuleCat.{u + 1} A) z).mapDerivedCategory
  have hg := congr_app (unboundedEtaleCompactSupport_baseChange_comp A sq sq' sq'') M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp] at hg
  apply (cancel_mono ((rightDerivedLowerShriekIso A k).hom.app _)).1
  rw [support_exchange_global A sq'' c k M]
  simp only [Category.assoc]
  rw [(rightDerivedLowerShriekIso A k).hom.naturality,
    reassoc_of% (support_exchange_global A sq' d k _),
    ← Category.assoc ((upperStar (ModuleCat.{u + 1} A) z).mapDerivedCategory.map _),
    ← Z.map_comp, support_exchange_global A sq c d M, Z.map_comp]
  simp only [Category.assoc]
  have hn := (unboundedEtaleUpperStarCompIso A z w).hom.naturality
    ((rightDerivedLowerShriekIso A c).hom.app M)
  change (upperStar (ModuleCat.{u + 1} A) (z ≫ w)).mapDerivedCategory.map
      ((rightDerivedLowerShriekIso A c).hom.app M) ≫
      (unboundedEtaleUpperStarCompIso A z w).hom.app _ =
    (unboundedEtaleUpperStarCompIso A z w).hom.app _ ≫
      Z.map (W.map ((rightDerivedLowerShriekIso A c).hom.app M)) at hn
  rw [hg]
  simpa only [Category.assoc] using hn =≫
    (Z.map ((unboundedEtaleCompactSupportBaseChange A sq).app M) ≫
      (unboundedEtaleCompactSupportBaseChange A sq').app _ ≫
      F₂.map ((unboundedEtaleUpperStarCompIso A z' w').inv.app M))

private lemma support_exchange_sum
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {w : X' ⟶ X} {w' : U' ⟶ U}
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e']
    [QuasiCompact e] [QuasiCompact e']
    (sq : IsPullback w' e' e w) (c : Compactification e) (d : Compactification e') :
    (mapDerivedCategoryEtaleLowerShriekBaseChangeIso (ModuleCat.{u + 1} A) sq).hom ≫
        Functor.whiskerRight (canonicalEtaleCompactSupportComparison A e c).inv
          (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory =
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) w').mapDerivedCategory
          (canonicalEtaleCompactSupportComparison A e' d).inv ≫
        (etaleNormalizedSupportExchange A sq c d).inv := by
  let B := ModuleCat.{u + 1} A
  let cp := c.ofIsPullback sq
  let t := rightDerivedLowerShriekOfCompactificationIso A cp d
  let V := (upperStar B w').mapDerivedCategory
  let W := (upperStar B w).mapDerivedCategory
  let α := mapDerivedCategoryEtaleLowerShriekBaseChangeIso B sq
  have ht : (canonicalEtaleCompactSupportComparison A e' d).inv ≫ t.inv =
      (canonicalEtaleCompactSupportComparison A e' cp).inv := by
    apply (cancel_mono (canonicalEtaleCompactSupportComparison A e' cp).hom).1
    have h := EtaleSupportExchange.comparison_refinement A e' cp d
    change t.hom ≫ (canonicalEtaleCompactSupportComparison A e' d).hom =
      (canonicalEtaleCompactSupportComparison A e' cp).hom at h
    rw [Category.assoc, ← h, ← Category.assoc t.inv]
    simp only [Iso.inv_hom_id, Category.id_comp]
    rw [h, Iso.inv_hom_id]
  have hg := transport_baseChange_diagram
    (etaleLowerShriek B e inferInstance).mapDerivedCategory
    (rightDerivedLowerShriekOfCompactification B c)
    (etaleLowerShriek B e' inferInstance).mapDerivedCategory
    (rightDerivedLowerShriekOfCompactification B cp)
    (upperStar B w).leftDerivedFunctor W
    (upperStar B w').leftDerivedFunctor V
    (leftDerivedUpperStarIsoMapDerivedCategory B w)
    (leftDerivedUpperStarIsoMapDerivedCategory B w')
    (derivedEtaleLowerShriekBaseChangeIso B sq)
    (GraphExchange.compactificationEtaleComparison B e c)
    (GraphExchange.compactificationEtaleComparison B e' cp)
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap B sq c)
    (GraphExchange.compactificationEtaleComparison_baseChange B sq c)
  have hc : (canonicalEtaleCompactSupportComparison A e c).inv =
      GraphExchange.compactificationEtaleComparison B e c := by
    simpa only [canonicalEtaleCompactSupportComparison, Iso.symm_inv, asIso_hom] using
      GraphExchange.graph_comparison_eq A e c
  have hd : (canonicalEtaleCompactSupportComparison A e' cp).inv =
      GraphExchange.compactificationEtaleComparison B e' cp := by
    simpa only [canonicalEtaleCompactSupportComparison, Iso.symm_inv, asIso_hom] using
      GraphExchange.graph_comparison_eq A e' cp
  rw [← hc, ← hd] at hg
  ext M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [etaleNormalizedSupportExchange, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc]
  rw [← Category.assoc, ← NatTrans.comp_app, ht]
  have h := congr_app hg M
  simp only [derivedEtaleLowerShriekBaseChangeIso, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] at h
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Iso.inv_hom_id_app_assoc] at h
  simp only [Functor.comp_obj] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring A
    isAddTorsion_of_finite (IsPullback.of_hasPullback c.g w)
  have := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap B sq c
  let C₀ := Functor.isoWhiskerLeft
      (rightDerivedLowerShriekOfCompactification B c)
      (leftDerivedUpperStarIsoMapDerivedCategory B w).symm ≪≫
    asIso (rightDerivedLowerShriekOfCompactificationBaseChangeMap B sq c) ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory B w') _
  change W.map ((canonicalEtaleCompactSupportComparison A e c).inv.app M) ≫
    C₀.hom.app M = α.inv.app M ≫
      (canonicalEtaleCompactSupportComparison A e' cp).inv.app (V.obj M) at h
  have h' := h =≫ C₀.inv.app M
  simp only [Category.assoc, Iso.hom_inv_id_app] at h'
  have hh : W.map ((canonicalEtaleCompactSupportComparison A e c).inv.app M) =
      α.inv.app M ≫ (canonicalEtaleCompactSupportComparison A e' cp).inv.app (V.obj M) ≫
        C₀.inv.app M := by
    calc
      _ = W.map ((canonicalEtaleCompactSupportComparison A e c).inv.app M) ≫ 𝟙 _ :=
        (Category.comp_id _).symm
      _ = _ := h'
  have hf := congrArg (fun f ↦ α.hom.app M ≫ f) hh
  simp only [Iso.hom_inv_id_app_assoc] at hf
  simpa only [C₀, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc] using hf

section

attribute [local irreducible] unboundedEtaleCompactSupportBaseChange
  unboundedEtaleLowerShriekCompIso etaleNormalizedSupportExchange etaleNormalizedSupportCompositor

end

/-- The normalized conjugates respect the actual compact-support compositor, at every K.
Source: Stacks Tags 0F7J, 0F7K, 03S6; blueprint etale locality Step 1.
(blueprint: lem-pur-etale-normalized-mates-composition-pasting).

Proof: Use the composition clause of lem-sfb-quasifinite-compact-support-exact to identify
   d_ve alpha with sigma (d_v S_e)(F_v d_e). The nested-summand counit calculation of
   lem-pur-etale-sum-composition-counit identifies sigma's conjugate with the canonical
   exact pullback compositor. Conjugate the equality using
   def-weil-pbc-adjunction-conjugate and lem-weil-pbc-mate-pasting(2). Vertical composition
   reverses; horizontal conjugacy gives rho_e G_v followed by e^* rho_v. This is the
   displayed equation, with c pointing out of G_ve. No inverse compositor is inserted.
   These are steps 1 and 2 of the DAG proof. -/
theorem etaleNormalizedMates_composition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X T : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian T]
    (e : U ⟶ X) (v : X ⟶ T)
    [Etale e] [Etale v] [IsSeparated e] [IsSeparated v]
    [QuasiCompact e] [QuasiCompact v]
    (c : Compactification e) (d : Compactification v) (k : Compactification (e ≫ v))
    (G_e : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (G_v : DerivedCategoryModule A T ⥤ DerivedCategoryModule A X)
    (G_ve : DerivedCategoryModule A T ⥤ DerivedCategoryModule A U)
    (adj_e : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G_e)
    (adj_v : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ G_v)
    (adj_ve : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) k ⊣ G_ve)
    (K : DerivedCategoryModule A T) :
    (conjugateIsoEquiv adj_ve
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (e ≫ v)
          inferInstance)
        (canonicalEtaleCompactSupportComparison A (e ≫ v) k).symm).hom.app K ≫
        (unboundedEtaleUpperStarCompIso A e v).hom.app K =
      (conjugateIsoEquiv adj_ve (adj_e.comp adj_v)
        (etaleNormalizedSupportCompositor A c d k)).hom.app K ≫
        (conjugateIsoEquiv adj_e
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
          inferInstance)
        (canonicalEtaleCompactSupportComparison A e c).symm).hom.app (G_v.obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map
          ((conjugateIsoEquiv adj_v
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v
          inferInstance)
        (canonicalEtaleCompactSupportComparison A v d).symm).hom.app K) := by
  let a_e := derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) e inferInstance
  let a_v := derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) v inferInstance
  let a_ve := derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) (e ≫ v) inferInstance
  let d_e := canonicalEtaleCompactSupportComparison A e c
  let d_v := canonicalEtaleCompactSupportComparison A v d
  let d_ve := canonicalEtaleCompactSupportComparison A (e ≫ v) k
  let α := etaleNormalizedSupportCompositor A c d k
  let σ := derivedEtaleSumCompIso A e v
  let δ := NatIso.hcomp d_e d_v
  have h := etaleSupportSumCompositor A e v c d k
  change α.hom ≫ d_ve.hom = δ.hom ≫ σ.hom at h
  have hi : σ.hom ≫ d_ve.inv = δ.inv ≫ α.hom := by
    apply (cancel_epi δ.hom).1
    rw [← Category.assoc, ← h]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, δ.hom_inv_id, Category.id_comp]
  have hc := conjugate_compositor_refinement a_e a_v a_ve adj_e adj_v adj_ve
    d_e.symm d_v.symm d_ve.symm σ α hi K
  simp only [conjugateIsoEquiv_apply_hom] at hc
  have hs := (etaleSumCompositionCounit A e v).2
  change conjugateEquiv a_ve (a_e.comp a_v) σ.hom =
    (unboundedEtaleUpperStarCompIso A e v).hom at hs
  rw [hs] at hc
  simpa only [conjugateIsoEquiv_apply_hom, Iso.symm_hom] using hc

/-- The identity normalization for every compactification and right adjunction.
Source: Stacks Tags 0F7J, 0F7K, 03S6; blueprint etale locality Step 1.
(blueprint: lem-pur-etale-normalized-mates-composition-pasting).

Proof: For the proper identity compactification the proper-support/sum comparison is the
   identity comparison by lem-sfb-quasifinite-compact-support-exact. Conjugacy with the
   identity adjunction gives the canonical right comparison. Step 3 transports this to
   every compactification by the refinement cocycle and conjugacy composition law. -/
theorem etaleNormalizedMates_identity
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X] (c : Compactification (𝟙 X))
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G) :
    (conjugateIsoEquiv adj
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X)
          inferInstance)
        (canonicalEtaleCompactSupportComparison A (𝟙 X) c).symm) ≪≫
        unboundedEtaleUpperStarIdIso A X =
      conjugateIsoEquiv adj (Adjunction.id (C := DerivedCategoryModule A X))
        ((rightDerivedLowerShriekOfCompactificationIso A
            (Compactification.ofIsProper (𝟙 X)) c).symm ≪≫
          identityEtaleCompactSupportComparison A X ≪≫
          Functor.mapDerivedCategoryNatIso
            (Adjunction.leftAdjointIdIso
              (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
                (𝟙 X) inferInstance) (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
          Functor.mapDerivedCategoryIdIso _).symm := by
  let a := derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) (𝟙 X) inferInstance
  let i := Functor.mapDerivedCategoryNatIso
      (Adjunction.leftAdjointIdIso
        (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X)
          inferInstance) (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
    Functor.mapDerivedCategoryIdIso _
  let cp := Compactification.ofIsProper (𝟙 X)
  let dp := canonicalEtaleCompactSupportComparison A (𝟙 X) cp
  let ap := a.ofNatIsoLeft dp.symm
  have hr := congrArg Iso.hom
    (EtaleSupportExchange.rightAdjointIso_refinement A (𝟙 X) cp c _ G ap adj)
  have hi : dp.inv ≫ (rightDerivedLowerShriekOfCompactificationIso A cp c).hom =
      (canonicalEtaleCompactSupportComparison A (𝟙 X) c).inv := by
    apply (conjugateEquiv adj a).injective
    rw [← conjugateEquiv_comp adj ap a]
    exact hr
  have hp := (etaleCompactSupportGraph_coherence A).identity X
  change dp = identityEtaleCompactSupportComparison A X at hp
  apply Iso.ext
  simp only [Iso.trans_hom, conjugateIsoEquiv_apply_hom, Iso.symm_hom]
  rw [← derived_sum_identity A X, conjugateEquiv_comp]
  apply congrArg (conjugateEquiv adj (Adjunction.id (C := DerivedCategoryModule A X)))
  simp only [Iso.trans_inv, Iso.symm_inv]
  rw [← hi, hp]
  simp only [Category.assoc]
  rfl

/-- The actual right exchange mates paste for an arbitrary further change of base.
Source: Stacks Tags 0F7J, 0F7K, 03S6; blueprint etale locality Step 1.
(blueprint: lem-pur-etale-normalized-mates-composition-pasting).

Proof: Step 4: set A_w = C_w inverse. Its right mate is B_w by the defining transpose.
   Invert the composite-base-change equation of
   lem-amb-unbounded-compact-support-comparisons. Apply
   lem-weil-pbc-mate-pasting(1) to A_w and A_z. This gives the equality after the two
   explicit pullback compositors. All adjunctions are unbounded. Open restriction is
   the special case where z is an open immersion. -/
theorem etaleNormalizedMates_baseChange_pasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' U'' X X' X'' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian U'']
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    {e : U ⟶ X} {e' : U' ⟶ X'} {e'' : U'' ⟶ X''}
    {w : X' ⟶ X} {z : X'' ⟶ X'} {w' : U' ⟶ U} {z' : U'' ⟶ U'}
    [Etale e] [Etale e'] [Etale e'']
    [IsSeparated e] [IsSeparated e'] [IsSeparated e'']
    [QuasiCompact e] [QuasiCompact e'] [QuasiCompact e'']
    (sq : IsPullback w' e' e w) (sq' : IsPullback z' e'' e' z)
    (sq'' : IsPullback (z' ≫ w') e'' e (z ≫ w))
    (c : Compactification e) (d : Compactification e') (k : Compactification e'')
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (G' : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (G'' : DerivedCategoryModule A X'' ⥤ DerivedCategoryModule A U'')
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ G')
    (adj'' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) k ⊣ G'')
    (K : DerivedCategoryModule A X) :
    (upperStar (ModuleCat.{u + 1} A) z').mapDerivedCategory.map
        ((etaleNormalizedRightExchange A sq c d G G' adj adj').app K) ≫
      (etaleNormalizedRightExchange A sq' d k G' G'' adj' adj'').app
        ((upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.obj K) =
    (unboundedEtaleUpperStarCompIso A z' w').inv.app (G.obj K) ≫
      (etaleNormalizedRightExchange A sq'' c k G G'' adj adj'').app K ≫
      G''.map ((unboundedEtaleUpperStarCompIso A z w).hom.app K) := by
  apply mates_paste adj adj' adj''
    (unboundedEtaleUpperStarCompIso A z' w')
    (unboundedEtaleUpperStarCompIso A z w)
    (TwoSquare.mk _ _ _ _ (etaleNormalizedSupportExchange A sq c d).inv)
    (TwoSquare.mk _ _ _ _ (etaleNormalizedSupportExchange A sq' d k).inv)
    (TwoSquare.mk _ _ _ _ (etaleNormalizedSupportExchange A sq'' c k).inv) _ K
  intro M
  let Z := (upperStar (ModuleCat.{u + 1} A) z).mapDerivedCategory
  let C₁ := etaleNormalizedSupportExchange A sq c d
  let C₂ := etaleNormalizedSupportExchange A sq' d k
  let C₃ := etaleNormalizedSupportExchange A sq'' c k
  let s := unboundedEtaleUpperStarCompIso A z' w'
  let t := unboundedEtaleUpperStarCompIso A z w
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) k
  change F.map (s.inv.app M) ≫ C₃.inv.app M ≫ t.hom.app _ =
    C₂.inv.app _ ≫ Z.map (C₁.inv.app M)
  apply (cancel_epi (t.hom.app _ ≫ Z.map (C₁.hom.app M) ≫ C₂.hom.app _)).1
  have hp := support_exchange_pasting A sq sq' sq'' c d k M
  change C₃.hom.app M = t.hom.app _ ≫ Z.map (C₁.hom.app M) ≫
    C₂.hom.app _ ≫ F.map (s.inv.app M) at hp
  have hp' := congrArg (fun f ↦ f ≫ C₃.inv.app M ≫ t.hom.app _) hp
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc] at hp'
  calc
    _ = t.hom.app _ := by simpa only [Category.assoc] using hp'.symm
    _ = _ := by
      symm
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Z.map_comp,
        Iso.hom_inv_id_app]
      change t.hom.app _ ≫ Z.map (𝟙 _) = t.hom.app _
      rw [Z.map_id]
      exact Category.comp_id _

/-- The canonical inverse-image square maps paste with their exact composition maps.
Source: Stacks Tags 0F7J, 0F7K, 03S6; blueprint etale locality Step 1.
(blueprint: lem-pur-etale-normalized-mates-composition-pasting).

Proof: Apply the sheaf square-pasting law to the two flipped squares, identify a
   flipped square comparison with the inverse comparison, and cancel the pullback
   compositors. Encode the two routes as finite pasting expressions of exact sheaf
   inverse images. The exact derived transformation pasting theorem descends their
   equality to the unbounded derived categories. Expand its word comparison formulas
   to identify each cell with exactDerivedSquareUpperStarIso or
   unboundedEtaleUpperStarCompIso. -/
theorem etaleNormalizedMates_pullback_pasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' U'' X X' X'' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian U'']
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    {e : U ⟶ X} {e' : U' ⟶ X'} {e'' : U'' ⟶ X''}
    {w : X' ⟶ X} {z : X'' ⟶ X'} {w' : U' ⟶ U} {z' : U'' ⟶ U'}
    [Etale e] [Etale e'] [Etale e'']
    [IsSeparated e] [IsSeparated e'] [IsSeparated e'']
    [QuasiCompact e] [QuasiCompact e'] [QuasiCompact e'']
    (sq : IsPullback w' e' e w) (sq' : IsPullback z' e'' e' z)
    (sq'' : IsPullback (z' ≫ w') e'' e (z ≫ w))
    (K : DerivedCategoryModule A X) :
    (upperStar (ModuleCat.{u + 1} A) z').mapDerivedCategory.map ((exactDerivedSquareUpperStarIso
        (ModuleCat.{u + 1} A) sq.toCommSq).inv.app K) ≫
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq'.toCommSq).inv.app ((upperStar
          (ModuleCat.{u + 1} A) w).mapDerivedCategory.obj K) =
    (unboundedEtaleUpperStarCompIso A z' w').inv.app
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ≫
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq''.toCommSq).inv.app K ≫
      (upperStar (ModuleCat.{u + 1} A) e'').mapDerivedCategory.map
        ((unboundedEtaleUpperStarCompIso A z w).hom.app K) := by
  exact etaleExactPullbackSquarePasting A sq sq' sq'' K

/-- The two normalized exchange squares imply the normalized square for the pasted base change.
Source: Stacks Tags 0F7J, 0F7K, 03S6; blueprint etale locality Step 1.
(blueprint: lem-pur-etale-normalized-mates-composition-pasting).

Proof: Step 7: substitute the mate-pasting equation of step 4. Substitute the two assumed
   rho B equations, moving rho through z'^* by functoriality. The resulting composite
   is chi_z z'^*(chi_w) times the pulled-back rho. Replace its first factors using
   step 6. Naturality of the canonical pullback compositors gives the displayed final
   equation. This is conditional: no normalization antecedent is silently assumed. -/
theorem etaleNormalizedMates_normalization_pasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' U'' X X' X'' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian U'']
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    {e : U ⟶ X} {e' : U' ⟶ X'} {e'' : U'' ⟶ X''}
    {w : X' ⟶ X} {z : X'' ⟶ X'} {w' : U' ⟶ U} {z' : U'' ⟶ U'}
    [Etale e] [Etale e'] [Etale e'']
    [IsSeparated e] [IsSeparated e'] [IsSeparated e'']
    [QuasiCompact e] [QuasiCompact e'] [QuasiCompact e'']
    (sq : IsPullback w' e' e w) (sq' : IsPullback z' e'' e' z)
    (sq'' : IsPullback (z' ≫ w') e'' e (z ≫ w))
    (c : Compactification e) (d : Compactification e') (k : Compactification e'')
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (G' : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (G'' : DerivedCategoryModule A X'' ⥤ DerivedCategoryModule A U'')
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ G')
    (adj'' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) k ⊣ G'')
    (K : DerivedCategoryModule A X)
    (hw : (etaleNormalizedRightExchange A sq c d G G' adj adj').app K ≫
        (conjugateIsoEquiv adj'
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e'
          inferInstance)
        (canonicalEtaleCompactSupportComparison A e' d).symm).hom.app ((upperStar (ModuleCat.{u + 1}
            A) w).mapDerivedCategory.obj K) =
      (upperStar (ModuleCat.{u + 1} A) w').mapDerivedCategory.map ((conjugateIsoEquiv adj
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
          inferInstance)
        (canonicalEtaleCompactSupportComparison A e c).symm).hom.app K) ≫
        (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).inv.app K)
    (hz : (etaleNormalizedRightExchange A sq' d k G' G'' adj' adj'').app
          ((upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.obj K) ≫
        (conjugateIsoEquiv adj''
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e''
          inferInstance)
        (canonicalEtaleCompactSupportComparison A e'' k).symm).hom.app
          ((upperStar (ModuleCat.{u + 1} A) z).mapDerivedCategory.obj ((upperStar (ModuleCat.{u + 1}
              A) w).mapDerivedCategory.obj K)) =
      (upperStar (ModuleCat.{u + 1} A) z').mapDerivedCategory.map
          ((conjugateIsoEquiv adj'
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e'
          inferInstance)
        (canonicalEtaleCompactSupportComparison A e' d).symm).hom.app ((upperStar (ModuleCat.{u + 1}
            A) w).mapDerivedCategory.obj K)) ≫
        (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq'.toCommSq).inv.app ((upperStar
            (ModuleCat.{u + 1} A) w).mapDerivedCategory.obj K)) :
    (etaleNormalizedRightExchange A sq'' c k G G'' adj adj'').app K ≫
        (conjugateIsoEquiv adj''
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e''
          inferInstance)
        (canonicalEtaleCompactSupportComparison A e'' k).symm).hom.app
          ((upperStar (ModuleCat.{u + 1} A) (z ≫ w)).mapDerivedCategory.obj K) =
      (upperStar (ModuleCat.{u + 1} A) (z' ≫ w')).mapDerivedCategory.map
          ((conjugateIsoEquiv adj
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
          inferInstance)
        (canonicalEtaleCompactSupportComparison A e c).symm).hom.app K) ≫
        (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq''.toCommSq).inv.app K := by
  exact normalization_pasting
    (unboundedEtaleUpperStarCompIso A z' w')
    (unboundedEtaleUpperStarCompIso A z w) _ _ _
    (etaleNormalizedRightExchange A sq c d G G' adj adj')
    (etaleNormalizedRightExchange A sq' d k G' G'' adj' adj'')
    (etaleNormalizedRightExchange A sq'' c k G G'' adj adj'')
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).inv
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq'.toCommSq).inv
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq''.toCommSq).inv K
    (etaleNormalizedMates_baseChange_pasting A sq sq' sq'' c d k G G' G'' adj adj' adj'' K)
    (etaleNormalizedMates_pullback_pasting A sq sq' sq'' K) hw hz

/-- The component of B is the adjunct specified in the node.
Source: Stacks Tags 0F7J, 0F7K, 03S6; blueprint etale locality Step 1.
(blueprint: lem-pur-etale-normalized-mates-composition-pasting).

Proof: Unfold the definition of etaleNormalizedRightExchange and apply
   def-weil-pbc-adjunction-mate's component formula. Its transpose is exactly the
   inverse exchange followed by w^* of the original counit. This also confirms that
   B is the actual mate on every unbounded K, rather than a freely chosen map. -/
theorem etaleNormalizedMates_exchange_adjunct
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}} [IsNoetherian U] [IsNoetherian U']
    [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {w : X' ⟶ X} {w' : U' ⟶ U}
    [Etale e] [IsSeparated e] [QuasiCompact e] [QuasiCompact e']
    (sq : IsPullback w' e' e w) (c : Compactification e) (d : Compactification e')
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (G' : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ G')
    (K : DerivedCategoryModule A X) :
    (etaleNormalizedRightExchange A sq c d G G' adj adj').app K =
      (adj'.homEquiv _ _)
        ((etaleNormalizedSupportExchange A sq c d).inv.app (G.obj K) ≫
          (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.map (adj.counit.app K)) := by
  apply (adj'.eq_homEquiv_apply _ _).2
  rw [adj'.homEquiv_counit]
  exact mateEquiv_counit adj adj'
    (TwoSquare.mk _ _ _ _ (etaleNormalizedSupportExchange A sq c d).inv) K

section

attribute [local irreducible] etaleNormalizedSupportExchange
  etaleNormalizedSupportCompositor etaleNormalizedRightExchange

end

/-- The normalization square is preserved by every Cartesian open restriction, at every K.
Source: Stacks Tags 0F7J, 0F7K, 03S6; blueprint etale locality Step 1.
(blueprint: lem-pur-etale-normalized-mates-composition-pasting).

Proof: Step 8 applies lem-pur-etale-support-exchange-right-mate to the open base change.
The theorem identifies the inverse actual exchange with the inverse sum exchange after
both graph comparisons. Conjugacy expresses the two compact-support counits through the
sum counits. Transpose both displayed sides through the sum adjunction: the sum counit's
base-change identity makes the transposes equal. Cancel the adjunction bijection. The
refinement equation identifies the result for every c and d. Applied to the further
base-changed arrow this is the open-restriction assertion; the B-pasting equation and
pullback-pasting equation identify it with the restriction of the original square. -/
theorem etaleNormalizedMates_openRestriction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}} [IsNoetherian U] [IsNoetherian U']
    [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {w : X' ⟶ X} {w' : U' ⟶ U}
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e']
    [QuasiCompact e] [QuasiCompact e'] [IsOpenImmersion w]
    (sq : IsPullback w' e' e w) (c : Compactification e) (d : Compactification e')
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (G' : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ G')
    (K : DerivedCategoryModule A X) :
    (etaleNormalizedRightExchange A sq c d G G' adj adj').app K ≫
        (conjugateIsoEquiv adj'
          (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e'
            inferInstance)
          (canonicalEtaleCompactSupportComparison A e' d).symm).hom.app
            ((upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.obj K) =
      (upperStar (ModuleCat.{u + 1} A) w').mapDerivedCategory.map
          ((conjugateIsoEquiv adj
            (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
              inferInstance)
            (canonicalEtaleCompactSupportComparison A e c).symm).hom.app K) ≫
        (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).inv.app K := by
  have h := EtaleSupportExchange.mate_refinement
    (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance) adj
    (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e' inferInstance) adj'
    (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) w').mapDerivedCategory
    (canonicalEtaleCompactSupportComparison A e c).inv
    (canonicalEtaleCompactSupportComparison A e' d).inv
    (TwoSquare.mk _ _ _ _
      (mapDerivedCategoryEtaleLowerShriekBaseChangeIso (ModuleCat.{u + 1} A) sq).hom)
    (TwoSquare.mk _ _ _ _ (etaleNormalizedSupportExchange A sq c d).inv)
    (support_exchange_sum A sq c d)
  rw [etaleExactSumBaseChangeMate A sq] at h
  exact (NatTrans.congr_app h K).symm

end AlgebraicGeometry.Etale
