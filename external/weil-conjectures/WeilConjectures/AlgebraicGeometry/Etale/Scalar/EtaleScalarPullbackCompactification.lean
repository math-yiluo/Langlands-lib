/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackComposition
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange

/-! # Scalar change and the compactification pullback compositor -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory upperStar openImmersionLowerShriek
  derivedTensor ProEtale.pbcFixedScalarExtension
attribute [local irreducible] scalarPullbackIso leftDerivedUpperStarCompactificationIso
  leftDerivedUpperStarComp leftDerivedUpperStarIsoMapDerivedCategory
  Functor.leftDerivedFunctorIsoMapDerivedCategory

-- Transport a composition square through arbitrary natural isomorphisms.
private theorem transport_composition
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (S₀ : C₀ ⥤ D₀) (S₁ : C₁ ⥤ D₁) (S₂ : C₂ ⥤ D₂)
    {F F' : C₀ ⥤ C₁} {G G' : C₁ ⥤ C₂} {H H' : C₀ ⥤ C₂}
    {P P' : D₀ ⥤ D₁} {Q Q' : D₁ ⥤ D₂} {R R' : D₀ ⥤ D₂}
    (eF : F ≅ F') (eG : G ≅ G') (eH : H ≅ H')
    (eP : P ≅ P') (eQ : Q ≅ Q') (eR : R ≅ R')
    (a : S₀ ⋙ P ≅ F ⋙ S₁) (b : S₁ ⋙ Q ≅ G ⋙ S₂)
    (t : S₀ ⋙ R ≅ H ⋙ S₂) (c : H' ≅ F' ⋙ G') (d : R' ≅ P' ⋙ Q')
    (X : C₀)
    (h : d.hom.app (S₀.obj X) ≫
        Q'.map (eP.inv.app (S₀.obj X) ≫ a.hom.app X ≫ S₁.map (eF.hom.app X)) ≫
        eQ.inv.app (S₁.obj (F'.obj X)) ≫ b.hom.app (F'.obj X) ≫
        S₂.map (eG.hom.app (F'.obj X)) =
      eR.inv.app (S₀.obj X) ≫ t.hom.app X ≫ S₂.map (eH.hom.app X) ≫
        S₂.map (c.hom.app X)) :
    (eR.hom.app (S₀.obj X) ≫ d.hom.app (S₀.obj X) ≫
        Q'.map (eP.inv.app (S₀.obj X)) ≫ eQ.inv.app (P.obj (S₀.obj X))) ≫
        Q.map (a.hom.app X) ≫ b.hom.app (F.obj X) =
      t.hom.app X ≫ S₂.map (eH.hom.app X ≫ c.hom.app X ≫
        G'.map (eF.inv.app X) ≫ eG.inv.app (F.obj X)) := by
  have hh := congrArg (fun z ↦ eR.hom.app (S₀.obj X) ≫ z ≫
    S₂.map (G'.map (eF.inv.app X) ≫ eG.inv.app (F.obj X))) h
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc] at hh
  have hnG := eG.hom.naturality (eF.inv.app X)
  have hnb := b.hom.naturality (eF.inv.app X)
  have hnQ := eQ.inv.naturality (S₁.map (eF.inv.app X))
  have hnQa := eQ.inv.naturality (a.hom.app X)
  simp only [Functor.comp_obj, Functor.comp_map] at hnb
  have hnG' : eG.hom.app (F'.obj X) ≫ G'.map (eF.inv.app X) ≫
      eG.inv.app (F.obj X) = G.map (eF.inv.app X) := by
    rw [← reassoc_of% hnG, Iso.hom_inv_id_app, Category.comp_id]
  have hmG := congrArg S₂.map hnG'
  simp only [Functor.map_comp] at hmG
  rw [hmG] at hh
  rw [← hnb, ← reassoc_of% hnQ] at hh
  have hmF : Q'.map (S₁.map (eF.hom.app X)) ≫
      Q'.map (S₁.map (eF.inv.app X)) = 𝟙 _ := by
    rw [← Q'.map_comp, ← S₁.map_comp, Iso.hom_inv_id_app, S₁.map_id, Q'.map_id]
  rw [reassoc_of% hmF, reassoc_of% hnQa] at hh
  simpa only [Functor.map_comp, Category.assoc] using hh

/-- Scalar change commutes with the canonical compactification pullback compositor.
Source: Stacks 0D6D and 03D8, scalar/pullback composition and transport through exact
inverse image; step 2 of lem-pur-etale-open-scalar-projection.
(blueprint: lem-pur-etale-scalar-pullback-compactification).

Proof: replace the indexed morphism f by j followed by g using c.comm. Apply the
existing exact scalarPullback_composition to j and g. Precompose its equality with
the exact/left-derived comparison for the B-pullback of f, and postcompose with
scalar extension of the inverse exact/left-derived comparison for j and g.
Naturality of the comparison for j moves the comparison for g across it;
naturality of scalarPullbackIso for j then cancels the comparison for g.
The resulting equality is the forward scalar/pullback composition equality for
the left-derived pullbacks, whose compositor is by definition the exact
compositor conjugated by these exact/left-derived comparisons. Regard each
composite as an isomorphism and take inverses. Transport through c.comm gives
the displayed formula. Only functoriality, naturality and inverse cancellation
are used; properness, flat coefficients and boundedness play no role. -/
theorem scalarPullback_compactification
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule A Y) :
    (scalarExtension φ X).map
        ((leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).hom.app K) ≫
      (scalarPullbackIso φ f).inv.app K =
    (scalarPullbackIso φ c.i).inv.app
        ((upperStar (ModuleCat.{u + 1} A) c.g).leftDerivedFunctor.obj K) ≫
      (upperStar (ModuleCat.{u + 1} B) c.i).leftDerivedFunctor.map
        ((scalarPullbackIso φ c.g).inv.app K) ≫
      (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} B) c).hom.app
        ((scalarExtension φ Y).obj K) := by
  let j := c.i
  let g := c.g
  let eA := fun {V W : Scheme.{u}} (p : V ⟶ W) ↦
    leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p
  let eB := fun {V W : Scheme.{u}} (p : V ⟶ W) ↦
    leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) p
  let cA := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) j g f c.comm) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm
  let cB := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} B) j g f c.comm) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm
  have h := scalarPullback_composition φ g j f c.comm.symm K
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] at h
  have ht := transport_composition (scalarExtension φ Y) (scalarExtension φ c.Z)
    (scalarExtension φ X) (eA g) (eA j) (eA f)
    (eB g) (eB j) (eB f)
    (scalarPullbackIso φ g) (scalarPullbackIso φ j) (scalarPullbackIso φ f)
    cA cB K (by
      simpa only [eA, eB, cA, cB, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.map_comp, Category.assoc] using h)
  have hf : (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) j g f c.comm).hom.app
        ((scalarExtension φ Y).obj K) ≫
      (upperStar (ModuleCat.{u + 1} B) j).leftDerivedFunctor.map
        ((scalarPullbackIso φ g).hom.app K) ≫
      (scalarPullbackIso φ j).hom.app
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) =
    (scalarPullbackIso φ f).hom.app K ≫ (scalarExtension φ X).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j g f c.comm).hom.app K) := by
    simpa only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
      Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory,
      eA, eB, cA, cB, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
      Iso.inv_hom_id_app_assoc] using ht
  have hi := congrArg Iso.inv (show
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} B) j g f c.comm).app
        ((scalarExtension φ Y).obj K) ≪≫
      (upperStar (ModuleCat.{u + 1} B) j).leftDerivedFunctor.mapIso
        ((scalarPullbackIso φ g).app K) ≪≫
      (scalarPullbackIso φ j).app
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) =
    (scalarPullbackIso φ f).app K ≪≫ (scalarExtension φ X).mapIso
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j g f c.comm).app K) from
    Iso.ext hf)
  simpa only [leftDerivedUpperStarCompactificationIso_eq, Iso.symm_hom,
    Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv, Category.assoc] using hi.symm

end AlgebraicGeometry.Etale
