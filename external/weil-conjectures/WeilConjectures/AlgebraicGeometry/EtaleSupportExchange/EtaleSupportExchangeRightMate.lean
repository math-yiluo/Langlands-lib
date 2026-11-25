/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Mathlib.CategoryTheory.Adjunction.Mates

import WeilConjectures.AlgebraicGeometry.Etale.Support.EtaleSupportMapCompatibility
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphCoherence
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
import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumExchangeCounit
public import WeilConjectures.AlgebraicGeometry.QuasiFinite.QuasiFiniteCompactSupportExact

/-! # The full right mate of etale compact-support exchange

Source: Stacks Project, Tag 03S6 (lemma-shriek-base-change); blueprint etale locality,
Step 1, and the proper/open normalization in lem-pur-etale-support-map-compatibility (1)
(blueprint: lem-pur-etale-support-exchange-right-mate).

The helpers assemble existing canonical maps. All equations concern natural transformations
on the ordinary unbounded categories, with arbitrary chosen right adjoints and adjunctions.
The comparison d is the inverse of the constructed graph map, not an arbitrary isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.EtaleSupportExchange

attribute [local irreducible] upperStar lowerStar etaleLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  canonicalEtaleCompactSupportComparison derivedEtaleLowerShriekUpperStarAdjunction
  exactCompactSupportExchange exactEtaleSumExchange

/-- The specified proper exchange followed by inverse open-extension exchange, as an iso.
The exact/left-derived inverse-image transports are those in exactCompactSupportExchange.
Invertibility uses the existing unbounded proper base-change theorem for finite coefficients.
Source: Stacks Tags 0F7L and 03S6
(blueprint: lem-pur-etale-support-exchange-right-mate). -/
noncomputable def exchangeIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X X' : Scheme.{u}} {e : U ⟶ X} (c : Compactification e) (w : X' ⟶ X) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd w e)).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (c.ofIsPullback (IsPullback.of_hasPullback w e).flip) :=
  haveI := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring A
    isAddTorsion_of_finite (IsPullback.of_hasPullback c.g w)
  haveI := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (ModuleCat.{u + 1} A) (IsPullback.of_hasPullback w e).flip c
  Functor.isoWhiskerLeft
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) w).symm ≪≫
    asIso (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback w e).flip c) ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.snd w e)) _

/-- Rho is the conjugate of the inverse canonical support/sum comparison.
Source: Stacks Tag 03S6; Mathlib Adjunction/Mates, conjugateIsoEquiv
(blueprint: lem-pur-etale-support-exchange-right-mate). -/
noncomputable def rightAdjointIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e)
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G) :
    G ≅ (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory :=
  conjugateIsoEquiv adj
    (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)
    (canonicalEtaleCompactSupportComparison A e c).symm

/-- The full right mate B for the pulled-back compactification and every unbounded input.
Its transpose is exactly the inverse exchange followed by the pulled-back counit.
Source: Stacks Tag 03S6; Mathlib Adjunction/Mates, mateEquiv
(blueprint: lem-pur-etale-support-exchange-right-mate). -/
noncomputable def rightMate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X X' : Scheme.{u}} {e : U ⟶ X} (c : Compactification e) (w : X' ⟶ X)
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (G' : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A (pullback w e))
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (c.ofIsPullback (IsPullback.of_hasPullback w e).flip) ⊣ G') :
    G ⋙ (upperStar (ModuleCat.{u + 1} A) (pullback.snd w e)).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory ⋙ G' :=
  (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ (exchangeIso A c w).inv))

/-- The inverse-comparison clause, as an equality of natural isomorphisms.
Source: Stacks Tag 03S6; support-map compatibility (1)
(blueprint: lem-pur-etale-support-exchange-right-mate).

Proof: Apply lem-pur-etale-support-map-compatibility (1) with (T,V,g,h) = (X,U,w,w').
The normalization in lem-amb-unbounded-compact-support-comparisons identifies its exchange
with exchangeIso. Invert the resulting equality and cancel the two support comparisons.
This gives C inverse after d' inverse equal to b inverse followed by w-star of d inverse.
All maps act on the entire unbounded categories. -/
theorem inverse_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X X' : Scheme.{u}} [IsLocallyNoetherian U] [CompactSpace U]
    [IsLocallyNoetherian X] [CompactSpace X] [IsLocallyNoetherian X'] [CompactSpace X']
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e) (w : X' ⟶ X) :
    Functor.isoWhiskerLeft
        (upperStar (ModuleCat.{u + 1} A) (pullback.snd w e)).mapDerivedCategory
        (canonicalEtaleCompactSupportComparison A (pullback.fst w e)
          (c.ofIsPullback (IsPullback.of_hasPullback w e).flip)).symm ≪≫
        (exchangeIso A c w).symm =
      (exactEtaleSumExchange A e w).symm ≪≫
        Functor.isoWhiskerRight (canonicalEtaleCompactSupportComparison A e c).symm
          (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory := by
  have h : exchangeIso A c w ≪≫ Functor.isoWhiskerLeft
        (upperStar (ModuleCat.{u + 1} A) (pullback.snd w e)).mapDerivedCategory
        (canonicalEtaleCompactSupportComparison A (pullback.fst w e)
          (c.ofIsPullback (IsPullback.of_hasPullback w e).flip)) =
      Functor.isoWhiskerRight (canonicalEtaleCompactSupportComparison A e c)
        (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory ≪≫
          exactEtaleSumExchange A e w := by
    apply Iso.ext
    simpa only [exchangeIso, exactCompactSupportExchange, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom, asIso_hom,
      canonicalEtaleCompactSupportCore, Category.assoc]
      using (etaleCompactSupportGraph_coherence A).base_change e c w
  exact congrArg Iso.symm h

/-- The displayed common sum-adjunction transpose, at every unbounded K.
Source: Stacks Tag 03S6 and blueprint etale locality Step 1
(blueprint: lem-pur-etale-support-exchange-right-mate).

Proof: Set M = G(K). First use inverse_comparison to replace C inverse after d' inverse.
Use the conjugate counit identity to replace epsilon after d inverse by evaluation after
S(rho). Naturality of inverse sum exchange moves rho across the exchange. Finally apply
lem-pur-etale-sum-exchange-counit on the whole unbounded category. This gives exactly the
four equalities of Step 3 in the DAG proof. Step 4 identifies the other transpose using
naturality of d' inverse and the defining adjunct of B. No cohomology detection is used. -/
theorem common_transpose
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X X' : Scheme.{u}} [IsLocallyNoetherian U] [CompactSpace U]
    [IsLocallyNoetherian X] [CompactSpace X] [IsLocallyNoetherian X'] [CompactSpace X']
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e) (w : X' ⟶ X)
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (K : DerivedCategoryModule A X) :
    (canonicalEtaleCompactSupportComparison A (pullback.fst w e)
          (c.ofIsPullback (IsPullback.of_hasPullback w e).flip)).inv.app
        ((upperStar (ModuleCat.{u + 1} A) (pullback.snd w e)).mapDerivedCategory.obj
          (G.obj K)) ≫
        (exchangeIso A c w).inv.app (G.obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.map (adj.counit.app K) =
      (etaleLowerShriek (ModuleCat.{u + 1} A) (pullback.fst w e)
          inferInstance).mapDerivedCategory.map
        ((upperStar (ModuleCat.{u + 1} A) (pullback.snd w e)).mapDerivedCategory.map
            ((rightAdjointIso A e c G adj).hom.app K) ≫
          (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A)
            (IsPullback.of_hasPullback w e).flip.toCommSq).inv.app K) ≫
        (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
          (pullback.fst w e) inferInstance).counit.app
          ((upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.obj K) := by
  let : IsNoetherian U := ⟨⟩
  let : IsNoetherian X := ⟨⟩
  let : IsNoetherian X' := ⟨⟩
  let S := (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory
  let S' := (etaleLowerShriek (ModuleCat.{u + 1} A)
    (pullback.fst w e) inferInstance).mapDerivedCategory
  let W := (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory
  let W' := (upperStar (ModuleCat.{u + 1} A) (pullback.snd w e)).mapDerivedCategory
  let ev := (derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) e inferInstance).counit
  let ev' := (derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) (pullback.fst w e) inferInstance).counit
  let rho := (rightAdjointIso A e c G adj).hom
  have hi := congrArg Iso.hom (inverse_comparison A e c w)
  have hiK := NatTrans.congr_app hi (G.obj K)
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app] at hiK
  have hc : S.map (rho.app K) ≫ ev.app K =
      (canonicalEtaleCompactSupportComparison A e c).inv.app (G.obj K) ≫
        adj.counit.app K :=
    conjugateEquiv_counit adj
      (derivedEtaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) e inferInstance) _ K
  have hn := (exactEtaleSumExchange A e w).inv.naturality (rho.app K)
  have he := (etaleSumExchangeCounit A e w).2.2.2.2.1 K
  have hflip : (Functor.mapDerivedCategorySquareIso
        (squareUpperStarIso (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback w e).toCommSq)).hom =
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback w e).flip.toCommSq).inv := by
    change (Functor.mapDerivedCategorySquareIso
      (squareUpperStarIso (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback w e).toCommSq)).hom =
      (Functor.mapDerivedCategorySquareIso
        (squareUpperStarIso (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback w e).toCommSq.flip)).inv
    rw [squareUpperStarIso_flip (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback w e).toCommSq]
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Category.assoc]
    have hi := Functor.mapDerivedCategoryNatIso_symm
      (squareUpperStarIso (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback w e).toCommSq).symm
    simpa only [Iso.symm_symm_eq] using congrArg (fun t ↦ _ ≫ t ≫ _) hi
  rw [hflip] at he
  rw [← Category.assoc, hiK, Category.assoc, ← W.map_comp, ← hc, W.map_comp]
  change (exactEtaleSumExchange A e w).inv.app (G.obj K) ≫
    W.map (S.map (rho.app K)) ≫ W.map (ev.app K) = _
  change S'.map (W'.map (rho.app K)) ≫
    (exactEtaleSumExchange A e w).inv.app
      ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) =
      (exactEtaleSumExchange A e w).inv.app (G.obj K) ≫
        W.map (S.map (rho.app K)) at hn
  rw [← Category.assoc, ← hn, Category.assoc, he, S'.map_comp, Category.assoc]

/-- The full right-adjoint exchange equation, as a natural-transformation identity.
Source: Stacks Tag 03S6 and blueprint etale locality Step 1
(blueprint: lem-pur-etale-support-exchange-right-mate).

Proof: Put M = G(K). By inverse_comparison, the transpose after d' inverse is the inverse
sum exchange followed by w-star of the compact-support counit after d inverse. The conjugate
counit identity changes this to w-star of evaluation after S(rho). Naturality of inverse
sum exchange moves rho across it. The derived counit equation of
lem-pur-etale-sum-exchange-counit then gives evaluation after S'(chi after w'-star rho).
On the other hand, the defining transpose of B and naturality of d' inverse give this same
transpose for rho' after B. Injectivity of the sum adjunction hom bijection proves the
equation at every K; naturality gives the displayed identity of natural transformations. -/
theorem rightMate_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X X' : Scheme.{u}} [IsLocallyNoetherian U] [CompactSpace U]
    [IsLocallyNoetherian X] [CompactSpace X] [IsLocallyNoetherian X'] [CompactSpace X']
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e) (w : X' ⟶ X)
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (G' : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A (pullback w e))
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adj' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (c.ofIsPullback (IsPullback.of_hasPullback w e).flip) ⊣ G') :
    rightMate A c w G G' adj adj' ≫
        Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory
          (rightAdjointIso A (pullback.fst w e)
            (c.ofIsPullback (IsPullback.of_hasPullback w e).flip) G' adj').hom =
      Functor.whiskerRight (rightAdjointIso A e c G adj).hom
          (upperStar (ModuleCat.{u + 1} A) (pullback.snd w e)).mapDerivedCategory ≫
        (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback w e).flip.toCommSq).inv := by
  let S' := (etaleLowerShriek (ModuleCat.{u + 1} A)
    (pullback.fst w e) inferInstance).mapDerivedCategory
  let sumAdj' := derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) (pullback.fst w e) inferInstance
  let d' := canonicalEtaleCompactSupportComparison A (pullback.fst w e)
    (c.ofIsPullback (IsPullback.of_hasPullback w e).flip)
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  apply (sumAdj'.homEquiv _ _).symm.injective
  change S'.map ((rightMate A c w G G' adj adj').app K ≫
      (rightAdjointIso A (pullback.fst w e) _ G' adj').hom.app
        ((upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.obj K)) ≫
      sumAdj'.counit.app _ = _
  have hc := conjugateEquiv_counit adj' sumAdj' d'.inv
    ((upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.obj K)
  change S'.map ((rightAdjointIso A (pullback.fst w e) _ G' adj').hom.app
    ((upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.obj K)) ≫ _ = _ at hc
  rw [S'.map_comp, Category.assoc, hc]
  have hn := d'.inv.naturality ((rightMate A c w G G' adj adj').app K)
  change S'.map ((rightMate A c w G G' adj adj').app K) ≫
    d'.inv.app (G'.obj ((upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.obj K)) =
      d'.inv.app _ ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (c.ofIsPullback (IsPullback.of_hasPullback w e).flip)).map
            ((rightMate A c w G G' adj adj').app K) at hn
  rw [← Category.assoc, hn, Category.assoc]
  have hb := mateEquiv_counit adj adj'
    (TwoSquare.mk _ _ _ _ (exchangeIso A c w).inv) K
  change (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (c.ofIsPullback (IsPullback.of_hasPullback w e).flip)).map
        ((rightMate A c w G G' adj adj').app K) ≫ adj'.counit.app _ =
      (exchangeIso A c w).inv.app (G.obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.map (adj.counit.app K) at hb
  change _ ≫ (_ ≫ adj'.counit.app _) = _
  rw [hb]
  exact common_transpose A e c w G adj K

private lemma mono_compactification_to_star_aux
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
    {U X : Scheme.{u}} {f : U ⟶ X} (c : Compactification f)
    (F : Sheaf U.smallEtaleTopology B)
    [Mono ((openImmersionLowerShriekToLowerStar B c.i).app F)] :
    Mono ((lowerStar B c.g).map ((openImmersionLowerShriekToLowerStar B c.i).app F) ≫
      (lowerStarComp B c.i c.g f c.comm).hom.app F) := by
  infer_instance

private lemma normalized_comparison_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (f : U ⟶ X) [Etale f] [IsSeparated f] [QuasiCompact f] (c : Compactification f)
    (a : etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (n : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory)
    (ha : ∀ M, a.app M ≫ (compactificationSheafToDirectImage A c).app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f M)
    (hn : ∀ P, n.inv.app (DerivedCategory.Qh.obj P) =
      compactSupportComparisonOnHomotopy A f c a P) :
    n = canonicalEtaleCompactSupportComparison A f c := by
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
  have hs : a = core.sheafComparison f c := by
    apply NatTrans.ext
    funext F
    apply (cancel_mono ((compactificationSheafToDirectImage A c).app F)).1
    rw [ha, core.sheaf_normalization]
  change n = core.comparison f c
  apply Iso.ext_inv
  apply (Functor.whiskeringLeft _ _ _).obj DerivedCategory.Qh |>.map_injective
  apply NatTrans.ext
  funext P
  change n.inv.app (DerivedCategory.Qh.obj P) =
    (core.comparison f c).inv.app (DerivedCategory.Qh.obj P)
  rw [hn, core.derived_normalization, hs]

private lemma comparison_refinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c d : Compactification e) :
    (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
      (canonicalEtaleCompactSupportComparison A e d).hom =
        (canonicalEtaleCompactSupportComparison A e c).hom := by
  obtain ⟨a, n, p, ha, hp, hb, hproj, hr⟩ := etaleSupportMapCompatibility A
  have hn (c : Compactification e) : n e c =
      canonicalEtaleCompactSupportComparison A e c :=
    normalized_comparison_eq A e c (a e c) (n e c) (ha e c).2.1 (ha e c).2.2
  have hc := hr e (Compactification.inf c d) c (Compactification.infFst c d)
  have hd := hr e (Compactification.inf c d) d (Compactification.infSnd c d)
  rw [hn, hn] at hc hd
  apply (cancel_epi
    (rightDerivedLowerShriekOfCompactificationIso A (Compactification.inf c d) c).hom).1
  rw [← Category.assoc, ← Iso.trans_hom,
    (unboundedEtaleCompactSupport_comparison_coherence A e).2, hd]
  exact hc.symm

/-- Rho agrees under every canonical compactification comparison, including proper refinements.
Source: Stacks Tags 0F7I, 0F7K, 0GKM
(blueprint: lem-pur-etale-support-exchange-right-mate).

Proof: For t : F(c) to F(d), compactification independence of the support comparison gives
d(d) after t = d(c) (lem-sfb-quasifinite-compact-support-exact). Invert and conjugate using
the contravariant composition law of def-weil-pbc-adjunction-conjugate. The result is
rho(c) after theta = rho(d). Common-refinement independence extends it to any c and d. -/
theorem rightAdjointIso_refinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsLocallyNoetherian U] [CompactSpace U]
    [IsLocallyNoetherian X] [CompactSpace X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c d : Compactification e)
    (G H : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (adjD : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ H) :
    conjugateIsoEquiv adjD adj (rightDerivedLowerShriekOfCompactificationIso A c d) ≪≫
        rightAdjointIso A e c G adj = rightAdjointIso A e d H adjD := by
  let : IsNoetherian U := ⟨⟩
  let : IsNoetherian X := ⟨⟩
  have hi : (canonicalEtaleCompactSupportComparison A e c).inv ≫
      (rightDerivedLowerShriekOfCompactificationIso A c d).hom =
        (canonicalEtaleCompactSupportComparison A e d).inv := by
    apply (cancel_mono (canonicalEtaleCompactSupportComparison A e d).hom).1
    rw [Category.assoc, comparison_refinement A e c d]
    simp
  apply Iso.ext
  change conjugateEquiv adjD adj _ ≫
    conjugateEquiv adj
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)
      _ = conjugateEquiv adjD _ _
  simp only [conjugateEquiv_comp, Iso.symm_hom, hi]

private lemma mate_refinement
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    {L₁' L₂' : E ⥤ F} {R₁' R₂' : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (a₁' : L₁' ⊣ R₁') (a₂' : L₂' ⊣ R₂')
    (W : D ⥤ F) (V : C ⥤ E)
    (t : L₁ ⟶ L₂) (t' : L₁' ⟶ L₂')
    (α : TwoSquare V L₁ L₁' W) (β : TwoSquare V L₂ L₂' W)
    (h : α ≫ Functor.whiskerRight t W =
      Functor.whiskerLeft V t' ≫ β) :
    Functor.whiskerRight (conjugateEquiv a₂ a₁ t) V ≫
        (mateEquiv a₁ a₁' α) =
      (mateEquiv a₂ a₂' β) ≫
        Functor.whiskerLeft W (conjugateEquiv a₂' a₁' t') := by
  ext K
  apply (a₁'.homEquiv _ _).symm.injective
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  change L₁'.map (_ ≫ _) ≫ a₁'.counit.app _ =
    L₁'.map (_ ≫ _) ≫ a₁'.counit.app _
  rw [L₁'.map_comp, L₁'.map_comp, Category.assoc, Category.assoc,
    mateEquiv_counit, conjugateEquiv_counit]
  have hn := α.naturality ((conjugateEquiv a₂ a₁ t).app K)
  change L₁'.map (V.map _) ≫ α.app _ = α.app _ ≫ W.map (L₁.map _) at hn
  rw [← Category.assoc, hn, Category.assoc, ← W.map_comp,
    conjugateEquiv_counit, W.map_comp, ← Category.assoc]
  have hK := NatTrans.congr_app h (R₂.obj K)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at hK
  rw [hK, Category.assoc, ← mateEquiv_counit a₂ a₂']
  simpa only [Category.assoc, Functor.comp_obj] using
    (t'.naturality ((mateEquiv a₂ a₂' β).app K)).symm =≫ a₂'.counit.app _

end AlgebraicGeometry.Etale.EtaleSupportExchange
