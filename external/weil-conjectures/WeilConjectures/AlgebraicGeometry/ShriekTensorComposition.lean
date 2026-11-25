/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.CompactificationProjectionComposition
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange

/-! # Tensor projection maps and compact-support composition

Source: Stacks Project, `more-etale.tex`, Tags 0F7B and 0F7J, and
`sites-cohomology.tex`, Tag 0E48 (auxiliary; not a blueprint node).

The projection map is the existing proper/open compactification construction with both
factors exchanged by the canonical signed derived tensor symmetry. Exact termwise inverse
image is identified with left derived inverse image by its canonical comparison.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

private theorem inverse_square
    {C : Type*} [Category C] {W X Y Z : C}
    (a : W ≅ X) (b : Y ≅ Z) (p : W ⟶ Y) (q : X ⟶ Z)
    (h : p ≫ b.hom = a.hom ≫ q) : q ≫ b.inv = a.inv ≫ p := by
  apply (cancel_mono b.hom).1
  simp only [Category.assoc, b.inv_hom_id, Category.comp_id, h, a.inv_hom_id_assoc]

private theorem projection_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F F' : C ⥤ D} {G : D ⥤ E} {H H' : C ⥤ E}
    (TD : D ⥤ D) (TE : E ⥤ E) (M N N' : C)
    (a : F' ≅ F) (b : H' ≅ H) (e : F' ⋙ G ≅ H')
    (pf : TD.obj (F.obj M) ⟶ F.obj N) (pf' : TD.obj (F'.obj M) ⟶ F'.obj N)
    (ph : TE.obj (H.obj M) ⟶ H.obj N') (ph' : TE.obj (H'.obj M) ⟶ H'.obj N')
    (q : N' ⟶ N) (pg : G ⋙ TE ⟶ TD ⋙ G)
    (hf : TD.map (a.hom.app M) ≫ pf = pf' ≫ a.hom.app N)
    (hh : ph' ≫ b.hom.app N' = TE.map (b.hom.app M) ≫ ph)
    (ht : pg.app (F'.obj M) ≫ G.map pf' ≫ e.hom.app N =
      TE.map (e.hom.app M) ≫ ph' ≫ H'.map q) :
    pg.app (F.obj M) ≫ G.map pf ≫
        (G.map (a.inv.app N) ≫ e.hom.app N ≫ b.hom.app N) =
      TE.map (G.map (a.inv.app M) ≫ e.hom.app M ≫ b.hom.app M) ≫ ph ≫ H.map q := by
  have hfi := inverse_square (TD.mapIso (a.app M)) (a.app N) pf' pf hf.symm
  have hfg := congrArg G.map hfi
  simp only [Functor.map_comp, Functor.mapIso_inv, Iso.app_inv] at hfg
  have hn := pg.naturality (a.inv.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Category.assoc, Functor.map_comp]
  rw [reassoc_of% hfg, ← reassoc_of% hn, reassoc_of% ht]
  rw [b.hom.naturality q, reassoc_of% hh]

namespace AlgebraicGeometry.Etale

section ProjectionProof
local instance essentiallySmall_etale_shriekTensorMain (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _
set_option backward.defeqAttrib.useBackward true
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize

set_option backward.isDefEq.respectTransparency false

-- Keep the large compactification and localization constructions behind their APIs.
attribute [local implicit_reducible] derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

attribute [local implicit_reducible] Compactification.restrict Compactification.ofIsPullback
  Compactification.comp Compactification.copy Compactification.postcomp

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor unboundedEtaleLowerShriekCompIso
  rightDerivedLowerShriekOfCompactificationIso
  rightDerivedLowerShriekOfCompactificationCompIso
  projectionMapOfCompactification derivedTensorSymmetry derivedTensor

-- The kernel checks the three specified compactification compositors.
private theorem projectionMap_compactification_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : Compactification f) (d : Compactification g)
    (h : Compactification (f ≫ g)) (e : Compactification (f ≫ d.i))
    [QuasiCompact f] [QuasiCompact (f ≫ g)]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Z) :
    let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
    let G := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d
    let H := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) h
    let T := derivedTensor (ModuleCat.{u + 1} A) X
    let U := derivedTensor (ModuleCat.{u + 1} A) Z
    let Lf := (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
    let Lg := (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor
    let E := Functor.isoWhiskerRight
      (rightDerivedLowerShriekOfCompactificationIso A e.restrict c).symm G ≪≫
      rightDerivedLowerShriekOfCompactificationCompIso A d e ≪≫
      rightDerivedLowerShriekOfCompactificationIso A (d.comp e) h
    ((projectionMapOfCompactification (ModuleCat.{u + 1} A) d).app (F.obj M)).app K ≫
        G.map (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app (Lg.obj K)) ≫
        E.hom.app ((T.obj M).obj (Lf.obj (Lg.obj K))) =
      (U.map (E.hom.app M)).app K ≫
        ((projectionMapOfCompactification (ModuleCat.{u + 1} A) h).app M).app K ≫
        H.map ((T.obj M).map ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K)) := by
  have ht := projection_transport (F := (rightDerivedLowerShriekOfCompactification (ModuleCat.{u +
    1} A) c)) (F' := (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) e.restrict))
    (G := (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d)) (H :=
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) h)) (H' :=
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) (d.comp e)))
    ((derivedTensor (ModuleCat.{u + 1} A) Y).flip.obj (((upperStar (ModuleCat.{u + 1} A)
      g).leftDerivedFunctor).obj K)) ((derivedTensor (ModuleCat.{u + 1} A) Z).flip.obj K) M
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj (((upperStar (ModuleCat.{u + 1} A)
      f).leftDerivedFunctor).obj (((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor).obj K)))
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj (((upperStar (ModuleCat.{u + 1} A) (f ≫
      g)).leftDerivedFunctor).obj K))
    (rightDerivedLowerShriekOfCompactificationIso A e.restrict c)
      (rightDerivedLowerShriekOfCompactificationIso A (d.comp e) h)
      (rightDerivedLowerShriekOfCompactificationCompIso A d e) (((projectionMapOfCompactification
      (ModuleCat.{u + 1} A) c).app M).app (((upperStar (ModuleCat.{u + 1} A)
      g).leftDerivedFunctor).obj K)) (((projectionMapOfCompactification (ModuleCat.{u + 1} A)
      e.restrict).app M).app
    (((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor).obj K))
      (((projectionMapOfCompactification (ModuleCat.{u + 1} A) h).app M).app K)
      (((projectionMapOfCompactification (ModuleCat.{u + 1} A) (d.comp e)).app M).app K)
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K)) (((flipFunctor _ _ _).map
    (projectionMapOfCompactification (ModuleCat.{u + 1} A) d)).app K)
    (projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso
      A e.restrict c M (((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor).obj K)).symm
    (projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso
      A (d.comp e) h M K)
    (projectionMapOfCompactification_tower_comp A f g d e M K)
  simpa only [flipFunctor, Functor.flip, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom,
    Category.assoc] using ht

end ProjectionProof

section TensorConventionProof
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize
local instance essentiallySmall_etale_tensorConvention (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor derivedTensorSymmetry derivedTensor
  unboundedEtaleLowerShriekCompIso projectionMapOfCompactification
attribute [local implicit_reducible] derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

private theorem projectionMap_chosen_comp_private
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Z) :
    let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
    let G := rightDerivedLowerShriek (ModuleCat.{u + 1} A) g
    let H := rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)
    let T := derivedTensor (ModuleCat.{u + 1} A) X
    let U := derivedTensor (ModuleCat.{u + 1} A) Z
    let Lf := (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
    let Lg := (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor
    let E := unboundedEtaleLowerShriekCompIso A f g
    ((projectionMap (ModuleCat.{u + 1} A) g).app (F.obj M)).app K ≫
        G.map (((projectionMap (ModuleCat.{u + 1} A) f).app M).app (Lg.obj K)) ≫
        E.hom.app ((T.obj M).obj (Lf.obj (Lg.obj K))) =
      (U.map (E.hom.app M)).app K ≫
        ((projectionMap (ModuleCat.{u + 1} A) (f ≫ g)).app M).app K ≫
        H.map ((T.obj M).map ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K)) := by
  simpa only [unboundedEtaleLowerShriekCompIso, projectionMap,
    rightDerivedLowerShriek, rightDerivedLowerShriekIso] using
    projectionMap_compactification_comp A f g
    (HasCompactification.compactification f)
    (HasCompactification.compactification g)
    (HasCompactification.compactification (f ≫ g))
    ((HasCompactification.compactification (f ≫ g)).ofComp
      (HasCompactification.compactification g)) M K

-- Normalize the two tensor conventions without unfolding the derived functors.

/-- Public export of the private `projectionMap_chosen_comp_private`
(used by `import all` importers; linter.privateModule). -/
alias projectionMap_chosen_comp := projectionMap_chosen_comp_private
end TensorConventionProof

set_option backward.isDefEq.respectTransparency false

end AlgebraicGeometry.Etale
