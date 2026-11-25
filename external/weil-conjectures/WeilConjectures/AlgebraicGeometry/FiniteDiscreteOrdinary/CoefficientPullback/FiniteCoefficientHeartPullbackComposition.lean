/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.CoefficientPullback.FiniteCoefficientHeartPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence

/-! # Composition of the specified comparison on coefficient hearts -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.CoefficientPullback

variable (A : Type u) [CommRing A]
  [TopologicalSpace A] [IsTopologicalRing A]
variable (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R]

omit [IsCommMonObj R] in
private theorem heartPush_comp (e : Mon.mk R ≅ Mon.mk (coefficient A))
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (EX : Encoding A X) (EY : Encoding A Y) (EZ : Encoding A Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)) :
    (heart A R e Z EZ).map ((CondensedRing.lowerStarComp R f g).hom.app M) ≫
      (heartPush A R e (f ≫ g) EX EZ).hom.app M =
    (heartPush A R e g EY EZ).hom.app ((CondensedRing.lowerStar R f).obj M) ≫
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).map
        ((heartPush A R e f EX EY).hom.app M) ≫
      (lowerStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g).hom.app
        ((heart A R e X EX).obj M) := by
  unfold heartPush heart encodingHeartPush
  ext V m
  dsimp [sectionHeartPushIso, sectionEncoding, fixedRestriction]
  simp only [CondensedRing.comapLowerStarIso, lowerStarComp_hom_app_hom_app]
  rfl

/-- The constructed heart comparison respects the published underived compositors.

Source: blueprint proper-base-change-finite, Transport and clause (2); the inverse-image
coefficient-encoding proof, steps 1--2; Stacks 03D3 and 0D6D.
(blueprint: lem-sfb-finite-coefficient-heart-pullback-composition).

Proof: The isomorphism heartPush is scalar restriction along the inverse coefficient
isomorphism followed by the normalized section-action comparison. The former has identity
underlying sheaf maps, by the coefficient-map naturality square. The latter has identity
underlying maps on every section. Hence the two composites of heartPush along f and g agree
with heartPush along f followed by g and the direct-image composition maps: after forgetting
module actions they are the same additive sheaf map induced by the canonical isomorphism
between iterated base change and base change along the composite. Faithfulness of the
forgetful functors proves the equality of module maps. Conjugate this equality under the
specified geometric adjunctions and the encoding equivalences. Conjugation reverses
composition and exchanges the two whiskerings. The published underived upperStarComp
is conjugate to lowerStarComp. The inverse-mate definition identifies
the conjugated heartPush with the explicitly constructed heartPull, so the conjugated
equality is the displayed equality. This argument is on hearts only. Neither localization
nor a derived direct image is used. The zero ring and empty schemes require no change. -/
theorem heartPull_comp (e : Mon.mk R ≅ Mon.mk (coefficient A))
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (EX : Encoding A X) (EY : Encoding A Y) (EZ : Encoding A Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj R Z)) :
    (heart A R e X EX).map ((CondensedRing.upperStarComp R f g).hom.app M) ≫
      (heartPull A R e f EX EY).hom.app ((CondensedRing.upperStar R g).obj M) ≫
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).map
        ((heartPull A R e g EY EZ).hom.app M) =
    (heartPull A R e (f ≫ g) EX EZ).hom.app M ≫
      (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g).hom.app
        ((heart A R e Z EZ).obj M) := by
  let ai (T U : Scheme.{u}) (h : T ⟶ U) := CondensedRing.upperStarLowerStarAdjunction R h
  let ao (T U : Scheme.{u}) (h : T ⟶ U) :=
    upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h
  let wi : TwoSquare (heart A R e Z EZ) (CondensedRing.upperStar R (f ≫ g))
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (f ≫ g))
      (heart A R e X EX) := (heartPull A R e (f ≫ g) EX EZ).inv
  let wg : TwoSquare (heart A R e Z EZ) (CondensedRing.upperStar R g)
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)
      (heart A R e Y EY) := (heartPull A R e g EY EZ).inv
  let wf : TwoSquare (heart A R e Y EY) (CondensedRing.upperStar R f)
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
      (heart A R e X EX) := (heartPull A R e f EX EY).inv
  have hw : wi.whiskerLeft (CondensedRing.upperStarComp R f g).hom =
      (TwoSquare.vComp wg wf).whiskerRight
        (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g).hom := by
    apply (mateEquiv ((ai Y Z g).comp (ai X Y f)) (ao X Z (f ≫ g))).injective
    rw [conjugateEquiv_mateEquiv_vcomp, mateEquiv_conjugateEquiv_vcomp,
      mateEquiv_hcomp]
    · dsimp only [wi, wg, wf, ai, ao]
      rw [heartPull_mate, heartPull_mate, heartPull_mate]
      rw [← conjugateIsoEquiv_apply_hom, CondensedRing.conjugateIsoEquiv_upperStarComp,
        ← conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_upperStarComp]
      refine NatTrans.ext (funext fun N ↦ ?_)
      simpa only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
        NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
        Category.id_comp, Category.assoc] using heartPush_comp A R e f g EX EY EZ N
  have hh := congr_app hw M
  dsimp only [wi, wg, wf, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    TwoSquare.vComp, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app] at hh
  simp only [Category.id_comp, Category.comp_id] at hh
  apply (cancel_epi ((heartPull A R e (f ≫ g) EX EZ).inv.app M)).mp
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc, hh]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.CoefficientPullback
