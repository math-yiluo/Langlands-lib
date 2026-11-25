/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfSupportedDiagonalData
import all WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons

/-! # Direct-image comparison restricted to the diagonal

Source: blueprint latest, thm-amb-p1-adjunction.proof.md, first triangle and the
interchange of the two coordinates under the direct image to the base.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale.SupportedTrace

open scoped CategoryTheory.Functor

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  rightDerivedLowerShriekCompIso rightDerivedLowerShriekCongrIso
attribute [local implicit_reducible] rightDerivedLowerShriek

-- Cancel the common final comparison in the two section-composition equations.
private theorem compare_sections {C : Type*} [Category C]
    {U V₁ V₂ W Z : C} (a₁ : V₁ ≅ U) (a₂ : V₂ ≅ U)
    (b₁ : V₁ ≅ W) (b₂ : V₂ ≅ W) (l : U ≅ Z) (c : W ≅ Z)
    (h₁ : a₁.hom ≫ l.hom = b₁.hom ≫ c.hom)
    (h₂ : a₂.hom ≫ l.hom = b₂.hom ≫ c.hom) :
    a₂.inv ≫ b₂.hom ≫ b₁.inv = a₁.inv := by
  apply (cancel_mono (a₁.hom ≫ l.hom)).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [h₁, Iso.inv_hom_id_assoc, ← h₂]
  simp

-- The compositor oriented towards a specified, equal composite morphism.
private def collapse (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    [IsProper f] [IsProper g] [IsProper h] (w : h = f ≫ g) :
    push A f ⋙ push A g ≅ push A h :=
  (rightDerivedLowerShriekCompIso A f g).symm ≪≫
    rightDerivedLowerShriekCongrIso A w.symm

private theorem compositor_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f] [IsProper g] :
    unboundedEtaleLowerShriekCompIso A f g =
      (rightDerivedLowerShriekCompIso A f g).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [unboundedEtaleLowerShriekCompIso, rightDerivedLowerShriekCompIso,
    Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc]
  rfl

private theorem congr_refl (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    rightDerivedLowerShriekCongrIso A (show f = f from rfl) = Iso.refl _ := by
  unfold rightDerivedLowerShriekCongrIso
  rfl

private theorem congr_inv (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} [HasCompactification f] [HasCompactification g]
    (w : f = g) :
    (rightDerivedLowerShriekCongrIso A w).inv =
      (rightDerivedLowerShriekCongrIso A w.symm).hom := by
  cases w
  simp only [rightDerivedLowerShriekCongrIso, Iso.refl_hom, Iso.refl_inv]

private theorem collapse_assoc (A : Type (u + 1)) [CommRing A] [Finite A]
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    [IsProper f] [IsProper g] [IsProper h]
    [IsProper fg] [IsProper gh] [IsProper fgh]
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)
    (M : DerivedCategoryModule A W) :
    (push A h).map ((collapse A f g fg hfg).hom.app M) ≫
        (collapse A fg h fgh hfgh).hom.app M =
      (collapse A g h gh hgh).hom.app ((push A f).obj M) ≫
        (collapse A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app M := by
  subst fg
  subst gh
  subst fgh
  let := unbounded_has_base_change A
  let := unbounded_has_proper_exchange A
  have q := (unboundedFormalism A).lowerShriekCompIso_assoc f g h
  simp only [unbounded_chosen_comp, compositor_eq] at q
  have hc : (unboundedFormalism A).lowerShriekCongr (Category.assoc f g h) =
      rightDerivedLowerShriekCongrIso A (Category.assoc f g h) := by
    generalize Category.assoc f g h = w
    cases w
    unfold rightDerivedLowerShriekCongrIso
    rfl
  rw [hc] at q
  have e := NatTrans.congr_app q M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at e
  change (push A h).map ((rightDerivedLowerShriekCompIso A f g).inv.app M) ≫
      (rightDerivedLowerShriekCompIso A (f ≫ g) h).inv.app M ≫
      (rightDerivedLowerShriekCongrIso A (Category.assoc f g h)).hom.app M =
    (rightDerivedLowerShriekCompIso A g h).inv.app ((push A f).obj M) ≫
      (rightDerivedLowerShriekCompIso A f (g ≫ h)).inv.app M at e
  apply (cancel_mono ((rightDerivedLowerShriekCongrIso A (Category.assoc f g h)).hom.app M)).1
  simpa only [collapse, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    congr_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id,
    Functor.map_comp, Functor.map_id, Category.assoc, ← congr_inv,
    Iso.inv_hom_id_app_assoc] using e

/-- Both ways to push a diagonal-supported object to the base agree.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, first triangle:
"The equality qp1=qp2 and the composition isomorphism for derived direct images
interchange these two operations"; Stacks Project, Tag 0DV0
(auxiliary; not a blueprint node).

Proof: expand directComparison as the inverse compositor for p2,f, the equality
p2 f = p1 f, and the compositor for p1,f. Expand the two section identifications
using Delta p_i = id. Apply associativity of the direct-image compositors to
Delta,p_i,f using the proved unbounded compact-support formalism. Cancel the
common comparisons for id,f and Delta,p_i f, then precompose with the inverse
identity comparison. No separate identity-composition law is needed. Congruence
along a reversed equality is the inverse congruence, by equality induction.
This argument concerns only composition of direct images; it uses neither tensor
products nor the projection formula, and holds for every diagonal-supported object. -/
theorem diagonalPushComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (M : DerivedCategoryModule A X) :
    (push A f).map ((TraceDiagonalDatum.idIsoDiagonalSnd (Λ := A) f).hom.app M) ≫
        (directComparison A f).hom.app ((push A (TraceDiagonalDatum.diagonal f)).obj M) =
      (push A f).map ((SfDiagonalKernel.diagonalFirst A f).hom.app M) := by
  have : IsProper (TraceDiagonalDatum.diagonal f) := by
    change IsProper (pullback.diagonal f)
    infer_instance
  have h₁ := collapse_assoc A (TraceDiagonalDatum.diagonal f) (pullback.fst f f) f
    (𝟙 X) (pullback.snd f f ≫ f) f (TraceDiagonalDatum.diagonal_fst f).symm
    (pullback.condition (f := f) (g := f)).symm (Category.id_comp f).symm M
  have h₂ := collapse_assoc A (TraceDiagonalDatum.diagonal f) (pullback.snd f f) f
    (𝟙 X) (pullback.snd f f ≫ f) f (TraceDiagonalDatum.diagonal_snd f).symm
    rfl (Category.id_comp f).symm M
  have h := compare_sections
    ((push A f).mapIso ((collapse A (TraceDiagonalDatum.diagonal f) (pullback.fst f f)
      (𝟙 X) (TraceDiagonalDatum.diagonal_fst f).symm).app M))
    ((push A f).mapIso ((collapse A (TraceDiagonalDatum.diagonal f) (pullback.snd f f)
      (𝟙 X) (TraceDiagonalDatum.diagonal_snd f).symm).app M))
    ((collapse A (pullback.fst f f) f (pullback.snd f f ≫ f)
      (pullback.condition (f := f) (g := f)).symm).app
        ((push A (TraceDiagonalDatum.diagonal f)).obj M))
    ((collapse A (pullback.snd f f) f (pullback.snd f f ≫ f) rfl).app
      ((push A (TraceDiagonalDatum.diagonal f)).obj M))
    ((collapse A (𝟙 X) f f (Category.id_comp f).symm).app M)
    ((collapse A (TraceDiagonalDatum.diagonal f) (pullback.snd f f ≫ f) f
      (by simp)).app M) h₁ h₂
  simp only [collapse, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Iso.app_hom, Iso.app_inv, Functor.mapIso_inv,
    congr_refl, Iso.refl_hom, Category.comp_id, congr_inv] at h
  simpa only [TraceDiagonalDatum.idIsoDiagonalSnd, SfDiagonalKernel.diagonalFirst,
    directComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc] using
      congrArg ((push A f).map
        ((rightDerivedLowerShriekIdIsoOfLowerStar (ModuleCat.{u + 1} A) X).inv.app M) ≫ ·) h

end AlgebraicGeometry.Etale.SupportedTrace
