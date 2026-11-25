/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionProper

import WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar
import all WeilConjectures.AlgebraicGeometry.ProperShriekCompCompForgetSupports
import all WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import all WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import all WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
import all WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionProper

/-! Compactification-level compositor and forget-supports calculation.
Source: blueprint latest, rank-one proof of proposition-purity-vector-bundles;
compatible-tower calculation as in the first triangle of thm-amb-p1-adjunction.proof.md.
(blueprint: lem-pur-coordinate-section-forget-supports)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] openImmersionLowerShriekUpperStarAdjunction
  Adjunction.mapDerivedCategoryAdjunction CategoryTheory.conjugateEquiv
  leftDerivedUpperStarComp derivedUpperStarLowerStarAdjunction
  derivedOpenImmersionLowerShriekToLowerStar openImmersionLowerShriekLowerStarExchange
  mapDerivedCategoryOpenImmersionLowerShriekComp mapDerivedCategoryOpenImmersionLowerShriekCongr
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Forget supports commutes with composition on compatible compactifications.
Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, first triangle, common pullback counits.

Proof: expand the compatible compositor into the open/proper exchange, the composition
of open extensions, and the ordinary proper direct-image compositor. Move the open
forget-supports map across exchange using its adjunction-unit mate equation. Composition
of the two open forget-supports maps is the forget-supports map for their composite,
by the composite counit formula and uniqueness of adjoints. Naturality and associativity
of the ordinary direct-image compositor then identify the remaining three proper
pushforward factors with the displayed compositor for p and f. The equality
`e.restrict.i ≫ pullback.fst e.g d.i = e.i` removes the final open congruence.
This calculation has no comparison between different compactifications.
(blueprint: lem-pur-coordinate-section-forget-supports)
-/
theorem coordinateSection_compactificationForgetSupports {W X S : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ S)
    (d : Compactification f) (e : Compactification (p ≫ d.i))
    (E : DerivedCategoryModule A W) :
    (rightDerivedLowerShriekOfCompactificationCompIso A d e).hom.app E ≫
        (compactificationForgetSupports (ModuleCat.{u + 1} A) (d.comp e)).app E =
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
          ((compactificationForgetSupports (ModuleCat.{u + 1} A) e.restrict).app E) ≫
        (compactificationForgetSupports (ModuleCat.{u + 1} A) d).app
          ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj E) ≫
        (rightDerivedLowerStarCompIsoOfComp
          (ModuleCat.{u + 1} A) p f (p ≫ f) rfl).hom.app E := by
  let B := ModuleCat.{u + 1} A
  simp only [rightDerivedLowerShriekOfCompactificationCompIso,
    compactificationForgetSupports, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, asIso_hom,
    Functor.comp_map, Functor.map_comp, Category.id_comp, Category.assoc,
    star_comp_iso_hom]
  have ho := open_compare_comp_congr A e.restrict.i (pullback.fst e.g d.i)
    e.i e.restrict_i_fst E
  have ho' := congrArg (fun t ↦ (lowerStar B (e.g ≫ d.g)).rightDerivedFunctor.map t) ho
  simp only [Functor.map_comp] at ho'
  erw [reassoc_of% ho']
  erw [← (rightDerivedLowerStarComp B e.g d.g).hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [star_comp_hom]
  erw [← (rightDerivedLowerStarCompHom B e.g d.g (e.g ≫ d.g) rfl).naturality_assoc,
    ← (rightDerivedLowerStarCompHom B e.g d.g (e.g ≫ d.g) rfl).naturality_assoc]
  simp only [Functor.comp_map]
  have h1 := rightDerivedLowerStarCompHom_assoc_app B e.i e.g d.g
    (p ≫ d.i) (e.g ≫ d.g) (p ≫ f) e.comm rfl
    (by rw [Category.assoc, ← d.comm]) E
  erw [h1]
  have h2 := rightDerivedLowerStarCompHom_assoc_app B e.restrict.i
    (pullback.fst e.g d.i) e.g e.i (e.restrict.g ≫ d.i) (p ≫ d.i)
    e.restrict_i_fst.symm e.isPullback_restrict.w e.comm E
  have h2' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) h2
  simp only [Functor.map_comp] at h2'
  erw [← reassoc_of% h2']
  have hn := (rightDerivedLowerStarCompHom B (pullback.fst e.g d.i) e.g
    (e.restrict.g ≫ d.i) e.isPullback_restrict.w).naturality
      ((derivedOpenImmersionLowerShriekToLowerStar B e.restrict.i).app E)
  have hn' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) hn
  simp only [Functor.comp_map, Functor.map_comp] at hn'
  erw [reassoc_of% hn']
  have hx := exchange_inclusion A (pullback.fst e.g d.i) e.restrict.g e.g d.i
    e.isPullback_restrict ((openImmersionLowerShriek B e.restrict.i).mapDerivedCategory.obj E)
  have hx' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) hx
  simp only [Functor.map_comp, star_comp_iso_hom] at hx'
  erw [reassoc_of% hx']
  have hn2 := (rightDerivedLowerStarCompHom B e.restrict.g d.i
    (e.restrict.g ≫ d.i) rfl).naturality
      ((derivedOpenImmersionLowerShriekToLowerStar B e.restrict.i).app E)
  have hn2' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) hn2
  simp only [Functor.comp_map, Functor.map_comp] at hn2'
  erw [← reassoc_of% hn2']
  have h3 := rightDerivedLowerStarCompHom_assoc_app B e.restrict.i e.restrict.g d.i
    p (e.restrict.g ≫ d.i) (p ≫ d.i) e.restrict.comm rfl rfl E
  have h3' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) h3
  simp only [Functor.map_comp] at h3'
  erw [reassoc_of% h3']
  have ht1 := (derivedOpenImmersionLowerShriekToLowerStar B d.i).naturality
    ((lowerStar B e.restrict.g).rightDerivedFunctor.map
      ((derivedOpenImmersionLowerShriekToLowerStar B e.restrict.i).app E))
  have ht1' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) ht1
  simp only [Functor.map_comp] at ht1'
  erw [← reassoc_of% ht1']
  have ht2 := (derivedOpenImmersionLowerShriekToLowerStar B d.i).naturality
    ((rightDerivedLowerStarCompHom B e.restrict.i e.restrict.g p e.restrict.comm).app E)
  have ht2' := congrArg (fun t ↦ (lowerStar B d.g).rightDerivedFunctor.map t) ht2
  simp only [Functor.map_comp] at ht2'
  erw [← reassoc_of% ht2']
  have h4 := rightDerivedLowerStarCompHom_assoc_app B p d.i d.g
    (p ≫ d.i) f (p ≫ f) rfl d.comm
    (by rw [Category.assoc, ← d.comm]) E
  erw [← h4]

end AlgebraicGeometry.Etale
