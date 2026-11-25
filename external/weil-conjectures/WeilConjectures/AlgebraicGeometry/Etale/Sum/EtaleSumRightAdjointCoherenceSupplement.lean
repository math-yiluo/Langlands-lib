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
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobeniusAdjunction
import WeilConjectures.AlgebraicGeometry.Etale.EtaleNormalizedMatesCompositionPasting
import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumExchangeCounit
import WeilConjectures.AlgebraicGeometry.EtaleSupportExchange.EtaleSupportExchangeRightMate
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.EtaleSumRightAdjointCoherence

/-! # Coherence of normalized etale sum right adjoints

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-co-smooth-etale-locality.proof.md, Step 1; Stacks Tags 03S6, 0F7J, 0F7K
(blueprint: lem-pur-etale-sum-right-adjoint-coherence).

The comparisons below use the actual proper/open compositor and exchange. The map to sum
extension is the constructed graph comparison, rather than a choice of a bare isomorphism.
Right adjoints and their adjunctions are quantified, so no choice of Brown adjoint is imposed.
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  canonicalEtaleCompactSupportComparison derivedEtaleLowerShriekUpperStarAdjunction
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso
  unboundedEtaleCompactSupportBaseChange exactEtaleSumExchange

/-- The normalization eta of the dualizing coefficient object.
Source: blueprint Step 1, definition of eta from rho at the coefficient unit
(blueprint: lem-pur-etale-sum-right-adjoint-coherence). -/
noncomputable def etaleSumRightAdjointUnitIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    [HasCompactification e]
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ⊣ G) :
    G.obj (constantComplex A X) ≅ constantComplex A U :=
  (etaleSumRightAdjointIso A e G adj).app (constantComplex A X) ≪≫
    etaleSumPullbackUnitIso A e

/-- The right-adjoint compositor is the conjugate of the specified compact-support compositor.
Source: Stacks Tags 0F7J, 0F7K; blueprint Step 1
(blueprint: lem-pur-etale-sum-right-adjoint-coherence). -/
noncomputable def etaleSumRightAdjointCompIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X T : Scheme.{u}} (e : U ⟶ X) (v : X ⟶ T)
    [HasCompactification e] [HasCompactification v] [HasCompactification (e ≫ v)]
    [QuasiCompact e] [QuasiCompact (e ≫ v)]
    (G_e : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (G_v : DerivedCategoryModule A T ⥤ DerivedCategoryModule A X)
    (G_ve : DerivedCategoryModule A T ⥤ DerivedCategoryModule A U)
    (adj_e : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ⊣ G_e)
    (adj_v : rightDerivedLowerShriek (ModuleCat.{u + 1} A) v ⊣ G_v)
    (adj_ve : rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e ≫ v) ⊣ G_ve) :
    G_ve ≅ G_v ⋙ G_e :=
  conjugateIsoEquiv adj_ve (adj_e.comp adj_v) (unboundedEtaleLowerShriekCompIso A e v)

/-- The exceptional exchange at the coefficient unit is the adjunct of the inverse
specified compact-support exchange followed by the pulled-back counit and unit identification.
Source: blueprint Step 1, definition of b; Stacks Tag 03S6
(blueprint: lem-pur-etale-sum-right-adjoint-coherence). -/
noncomputable def etaleSumRightAdjointBaseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {w : X' ⟶ X} {w' : U' ⟶ U}
    [Etale e] [IsSeparated e] [QuasiCompact e] [QuasiCompact e']
    [HasCompactification e] [HasCompactification e'] (sq : IsPullback w' e' e w)
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (G' : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ⊣ G)
    (adj' : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e' ⊣ G') :
    (upperStar (ModuleCat.{u + 1} A) w').mapDerivedCategory.obj
        (G.obj (constantComplex A X)) ⟶ G'.obj (constantComplex A X') :=
  haveI := (unboundedEtaleCompactSupport_baseChange A sq).1
  (adj'.homEquiv _ _)
    (inv ((unboundedEtaleCompactSupportBaseChange A sq).app
        (G.obj (constantComplex A X))) ≫
      (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.map
        (adj.counit.app (constantComplex A X)) ≫ (etaleSumPullbackUnitIso A w).hom)

private theorem comparison_symm
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c d : Compactification e) :
    (rightDerivedLowerShriekOfCompactificationIso A c d).symm =
      rightDerivedLowerShriekOfCompactificationIso A d c := by
  apply Iso.ext
  apply (cancel_epi (rightDerivedLowerShriekOfCompactificationIso A c d).hom).mp
  have h := (unboundedEtaleCompactSupport_comparison_coherence A e).2 c d c
  rw [(unboundedEtaleCompactSupport_comparison_coherence A e).1 c] at h
  simpa only [Iso.trans_hom, Iso.refl_hom, Iso.symm_hom, Iso.hom_inv_id] using
    (congrArg Iso.hom h).symm

private theorem support_iso_chosen
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e] [HasCompactification e] :
    etaleSumSupportIso A e =
      canonicalEtaleCompactSupportComparison A e (HasCompactification.compactification e) := by
  unfold etaleSumSupportIso rightDerivedLowerShriekIso
  rw [(unboundedEtaleCompactSupport_comparison_coherence A e).1]
  exact Iso.refl_trans _

private theorem pullback_unit_comp
    (A : Type (u + 1)) [CommRing A]
    {U X T : Scheme.{u}} (e : U ⟶ X) (v : X ⟶ T) :
    (unboundedEtaleUpperStarCompIso A e v).hom.app (constantComplex A T) ≫
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map
          (etaleSumPullbackUnitIso A v).hom ≫ (etaleSumPullbackUnitIso A e).hom =
      (etaleSumPullbackUnitIso A (e ≫ v)).hom := by
  have h := leftDerivedUpperStarComp_hom_app_unit
    (ModuleCat.{u + 1} A) e v (e ≫ v) rfl
  simp only [← leftDerivedUpperStarUnitIso_hom_eq_η] at h
  apply (cancel_epi ((leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) (e ≫ v)).hom.app (constantComplex A T))).mp
  simp only [etaleSumPullbackUnitIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  dsimp only [constantComplex] at *
  rw [(leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) e).inv.naturality_assoc]
  rw [(leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) e).inv.naturality_assoc]
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, unboundedEtaleUpperStarCompIso,
    leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app_assoc] at h ⊢
  let i := (upperStar (ModuleCat.{u + 1} A) e).leftDerivedFunctorIsoMapDerivedCategory
  rw [← i.inv.naturality_assoc]
  exact h

private theorem pullback_unit_comp_eq
    (A : Type (u + 1)) [CommRing A]
    {U X T : Scheme.{u}} (e : U ⟶ X) (v : X ⟶ T) (ev : U ⟶ T)
    (h : ev = e ≫ v) :
    (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) e v ev h) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm).hom.app (constantComplex A T) ≫
      (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map
        (etaleSumPullbackUnitIso A v).hom ≫ (etaleSumPullbackUnitIso A e).hom =
      (etaleSumPullbackUnitIso A ev).hom := by
  subst ev
  exact pullback_unit_comp A e v

private theorem pullback_unit_square
    (A : Type (u + 1)) [CommRing A]
    {U U' X X' : Scheme.{u}}
    {e : U ⟶ X} {e' : U' ⟶ X'} {w : X' ⟶ X} {w' : U' ⟶ U}
    (sq : CommSq w' e' e w) :
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).inv.app
        (constantComplex A X) ≫
      (upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory.map
        (etaleSumPullbackUnitIso A w).hom ≫ (etaleSumPullbackUnitIso A e').hom =
      (upperStar (ModuleCat.{u + 1} A) w').mapDerivedCategory.map
        (etaleSumPullbackUnitIso A e).hom ≫ (etaleSumPullbackUnitIso A w').hom := by
  have h₁ := pullback_unit_comp_eq A e' w (w' ≫ e) sq.w
  have h₂ := pullback_unit_comp_eq A w' e (w' ≫ e) rfl
  have hh : exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq =
      (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A)
        e' w (w' ≫ e) sq.w) ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm).symm ≪≫
      unboundedEtaleUpperStarCompIso A w' e := by
    ext K
    simp only [exactDerivedSquareUpperStarIso, squareUpperStarIso,
      Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
      unboundedEtaleUpperStarCompIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Iso.symm_inv, NatTrans.comp_app, Category.assoc]
  rw [hh]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc]
  rw [h₁]
  apply (cancel_epi ((unboundedEtaleUpperStarCompIso A w' e).hom.app
    (constantComplex A X))).mp
  simpa only [Iso.hom_inv_id_app_assoc, unboundedEtaleUpperStarCompIso] using h₂.symm

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

private theorem baseChange_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {w : X' ⟶ X} {w' : U' ⟶ U}
    [Etale e] [IsSeparated e] [QuasiCompact e] [QuasiCompact e']
    [HasCompactification e] [HasCompactification e'] (sq : IsPullback w' e' e w)
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (G' : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ⊣ G)
    (adj' : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e' ⊣ G') :
    etaleSumRightAdjointBaseChange A sq G G' adj adj' =
      (etaleNormalizedRightExchange A sq (HasCompactification.compactification e)
        (HasCompactification.compactification e') G G' adj adj').app (constantComplex A X) ≫
      G'.map (etaleSumPullbackUnitIso A w).hom := by
  have := (unboundedEtaleCompactSupport_baseChange A sq).1
  have hc : inv ((unboundedEtaleCompactSupportBaseChange A sq).app
      (G.obj (constantComplex A X))) =
      (etaleNormalizedSupportExchange A sq (HasCompactification.compactification e)
        (HasCompactification.compactification e')).inv.app (G.obj (constantComplex A X)) := by
    apply (cancel_epi ((unboundedEtaleCompactSupportBaseChange A sq).app
      (G.obj (constantComplex A X)))).mp
    rw [IsIso.hom_inv_id]
    rw [congrArg (fun t ↦ t.app (G.obj (constantComplex A X))) (chosen_exchange A sq)]
    exact (Iso.hom_inv_id_app _ _).symm
  rw [etaleNormalizedMates_exchange_adjunct]
  erw [← adj'.homEquiv_naturality_right]
  unfold etaleSumRightAdjointBaseChange
  rw [hc]
  congr 1
  exact (Category.assoc _ _ _).symm

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

/-- Composition coherence for the normalized right adjoints, at every unbounded input.
Source: blueprint Step 1; Stacks Tags 0F7J, 0F7K
(blueprint: lem-pur-etale-sum-right-adjoint-coherence).

Proof: The sum adjunction counit folds each summand; after two extensions it sends a nested
summand to its original section. Sheafification proves equality of the two sheaf counits.
Apply this degreewise and descend through localization, using
lemma-affine-space-etale-localization--4 and lem-weil-pbc-localization-universal-property.
The proper-support/sum comparison of lem-sfb-quasifinite-compact-support-exact intertwines
this sum compositor with the actual compact-support compositor. Conjugate that equality
using def-weil-pbc-adjunction-conjugate and lem-weil-pbc-mate-pasting. The conjugate of the
sum compositor is the pullback compositor by the counit calculation. This gives the equation.
No boundedness or constructibility assumption occurs in the degreewise argument. -/
theorem etaleSumRightAdjoint_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X T : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian T]
    (e : U ⟶ X) (v : X ⟶ T)
    [Etale e] [Etale v] [IsSeparated e] [IsSeparated v]
    [QuasiCompact e] [QuasiCompact v]
    [HasCompactification e] [HasCompactification v] [HasCompactification (e ≫ v)]
    (G_e : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (G_v : DerivedCategoryModule A T ⥤ DerivedCategoryModule A X)
    (G_ve : DerivedCategoryModule A T ⥤ DerivedCategoryModule A U)
    (adj_e : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ⊣ G_e)
    (adj_v : rightDerivedLowerShriek (ModuleCat.{u + 1} A) v ⊣ G_v)
    (adj_ve : rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e ≫ v) ⊣ G_ve)
    (K : DerivedCategoryModule A T) :
    (etaleSumRightAdjointIso A (e ≫ v) G_ve adj_ve).hom.app K ≫
        (unboundedEtaleUpperStarCompIso A e v).hom.app K =
      (etaleSumRightAdjointCompIso A e v G_e G_v G_ve adj_e adj_v adj_ve).hom.app K ≫
        (etaleSumRightAdjointIso A e G_e adj_e).hom.app (G_v.obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map
          ((etaleSumRightAdjointIso A v G_v adj_v).hom.app K) := by
  have h := etaleNormalizedMates_composition A e v
    (HasCompactification.compactification e) (HasCompactification.compactification v)
    (HasCompactification.compactification (e ≫ v)) G_e G_v G_ve adj_e adj_v adj_ve K
  have hc : etaleNormalizedSupportCompositor A
      (HasCompactification.compactification e) (HasCompactification.compactification v)
      (HasCompactification.compactification (e ≫ v)) =
      unboundedEtaleLowerShriekCompIso A e v := by
    unfold etaleNormalizedSupportCompositor unboundedEtaleLowerShriekCompIso
      rightDerivedLowerShriekIso
    rw [comparison_symm A e]
    rfl
  rw [hc] at h
  simp only [etaleSumRightAdjointIso, support_iso_chosen,
    etaleSumRightAdjointCompIso]
  convert h using 1

/-- The identity normalization uses the canonical identity comparison.
Source: blueprint Step 1; Stacks Tag 0F7K
(blueprint: lem-pur-etale-sum-right-adjoint-coherence).

Proof: The proper-support comparison of the identity compactification is the canonical
identity sum comparison (lem-sfb-quasifinite-compact-support-exact). Its conjugate is the
identity pullback comparison by def-weil-pbc-composite-adjunction and
 def-weil-pbc-adjunction-conjugate. Canonical refinement comparisons give the same equation
for the chosen compactification. -/
theorem etaleSumRightAdjoint_id
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [IsNoetherian X] [HasCompactification (𝟙 X)]
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 X) ⊣ G) :
    etaleSumRightAdjointIso A (𝟙 X) G adj ≪≫ unboundedEtaleUpperStarIdIso A X =
      conjugateIsoEquiv adj (Adjunction.id (C := DerivedCategoryModule A X))
        (unboundedEtaleLowerShriekId A X).symm := by
  have hid := (unboundedEtaleCompactSupport_comparison_coherence A (𝟙 X)).1
  simpa only [etaleSumRightAdjointIso, etaleSumSupportIso, rightDerivedLowerShriekIso,
    rightDerivedLowerShriek,
    hid, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl, unboundedEtaleLowerShriekId] using
    etaleNormalizedMates_identity A X (HasCompactification.compactification (𝟙 X)) G adj

/-- Base change preserves the normalized dualizing coefficient object.
Source: blueprint Step 1; Stacks Tag 03S6
(blueprint: lem-pur-etale-sum-right-adjoint-coherence).

Proof: Expand the adjunction conjugate to express the compact-support counit as the sum
counit after d and rho. The specified sheaf sum base-change map is the mate of the pullback
square: expand its definition as the conjugate of underived exchange, paste the inverse-image
and sum adjunctions, and cancel their triangles (lem-weil-pbc-mate-pasting). Its counit square
therefore commutes. Apply this degreewise to unbounded representatives and use localization.
The actual proper/open exchange intertwines d with the inverse sum exchange by
lem-pur-etale-support-map-compatibility (1), for arbitrary w, including non-finite proper
compactification factors. Transpose the defining counit composite of b across the sum
adjunction, substitute these two identities, and cancel the injective hom bijection. At A_X
the pullback-unit identifications give exactly the displayed equality. -/
theorem etaleSumRightAdjoint_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' X X' : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian U'] [IsNoetherian X] [IsNoetherian X']
    {e : U ⟶ X} {e' : U' ⟶ X'} {w : X' ⟶ X} {w' : U' ⟶ U}
    [Etale e] [Etale e'] [IsSeparated e] [IsSeparated e']
    [QuasiCompact e] [QuasiCompact e']
    [HasCompactification e] [HasCompactification e'] (sq : IsPullback w' e' e w)
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (G' : DerivedCategoryModule A X' ⥤ DerivedCategoryModule A U')
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ⊣ G)
    (adj' : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e' ⊣ G') :
    etaleSumRightAdjointBaseChange A sq G G' adj adj' ≫
        (etaleSumRightAdjointUnitIso A e' G' adj').hom =
      (upperStar (ModuleCat.{u + 1} A) w').mapDerivedCategory.map
        (etaleSumRightAdjointUnitIso A e G adj).hom ≫
          (etaleSumPullbackUnitIso A w').hom := by
  have h := normalized_square A sq (HasCompactification.compactification e)
    (HasCompactification.compactification e') G G' adj adj' (constantComplex A X)
  have hρ : (etaleNormalizedRightExchange A sq (HasCompactification.compactification e)
      (HasCompactification.compactification e') G G' adj adj').app (constantComplex A X) ≫
      (etaleSumRightAdjointIso A e' G' adj').hom.app
        ((upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory.obj (constantComplex A X)) =
      (upperStar (ModuleCat.{u + 1} A) w').mapDerivedCategory.map
        ((etaleSumRightAdjointIso A e G adj).hom.app (constantComplex A X)) ≫
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).inv.app
        (constantComplex A X) := by
    simp only [etaleSumRightAdjointIso, support_iso_chosen]
    unfold EtaleSupportExchange.rightAdjointIso at h
    convert h using 1
  rw [baseChange_eq]
  simp only [etaleSumRightAdjointUnitIso, Iso.trans_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  rw [(etaleSumRightAdjointIso A e' G' adj').hom.naturality_assoc]
  rw [← Category.assoc, ← Category.assoc, hρ]
  simp only [Category.assoc]
  rw [pullback_unit_square]

end AlgebraicGeometry.Etale
