/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleTopos
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineEtaleSiteBaseChange
import WeilConjectures.AlgebraicGeometry.AffineEtaleRestrictionUnit
import WeilConjectures.AlgebraicGeometry.AffineEtaleRestrictionComposition

/-!
# Comparison of inverse images on the full and affine étale sites

Source: Stacks Project, Étale Cohomology 09YQ, Topologies 04HR
(blueprint: lem-weil-pbc-sets-affine-etale-inverse-image-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks 09YQ, using 04HR
(blueprint: lem-weil-pbc-sets-affine-etale-inverse-image-comparison).
The functors `U` are base change, specified by their identifications `t` with small-site
base change. `L` and `a` are the affine-site inverse images and their adjunctions.
The comparisons `e` preserve units. The composition comparisons `c` and `d` are specified
by their unit equations; `gamma` is the canonical iterated-base-change identification.

Proof:
1. Affine base change preserves affine étale objects and standard finite coverings
   (lem-weil-pbc-affine-etale-site-base-change), hence is continuous.
2. Restriction is an equivalence (lem-weil-pbc-affine-etale-site-topos). Full and affine
   direct images agree after restriction, since both evaluate at the same base change
   (situation-conventions, def-weil-pbc-sites-and-cohomology).
   Transport the inverse-image adjunction across these equivalences. Uniqueness of left
   adjoints gives e, with its unit equation (situation-conventions).
   Finite-limit preservation transfers from the full-site inverse image.
3. Evaluate the unit equation on each affine object. For composites, pullback pasting
   (def-pc-fibre-product) gives gamma. Both routes preserve the iterated units by
   lem-weil-pbc-sets-etale-inverse-image-composition-units and
   lem-weil-pbc-site-morphism-composition. Uniqueness of the unit-compatible adjoint
   comparison (situation-conventions) makes the two routes equal. -/
theorem exists_affineEtale_inverseImage_comparison :
    ∃ (U : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        X.FullAffineEtale ⥤ Y.FullAffineEtale)
      (t : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        U h ⋙ fullAffineEtaleInclusion Y ≅
          fullAffineEtaleInclusion X ⋙ (MorphismProperty.Over.pullback @Etale ⊤ h)),
    (∀ (X Y : Scheme.{u}) (h : Y ⟶ X) [IsAffineHom h]
      (V : X.FullAffineEtale) (R : Presieve V),
      R ∈ fullAffineEtalePrecoverage X V →
        R.map (U h) ∈ fullAffineEtalePrecoverage Y ((U h).obj V)) ∧
    ∃ (_ : ∀ (X Y : Scheme.{u}) (h : Y ⟶ X) [IsAffineHom h],
        (U h).IsContinuous (fullAffineEtaleTopology X) (fullAffineEtaleTopology Y))
      (L : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        Sheaf (fullAffineEtaleTopology X) (Type (u + 1)) ⥤
          Sheaf (fullAffineEtaleTopology Y) (Type (u + 1)))
      (a : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        L h ⊣ (U h).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology X) (fullAffineEtaleTopology Y))
      (e : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        etaleSetPullback h ⋙ ((fullAffineEtaleInclusion Y).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology Y) Y.smallEtaleTopology) ≅
          ((fullAffineEtaleInclusion X).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology X) X.smallEtaleTopology) ⋙ L h),
    (∀ (X Y : Scheme.{u}) (h : Y ⟶ X) [IsAffineHom h], PreservesFiniteLimits (L h)) ∧
    (∀ (X Y : Scheme.{u}) (h : Y ⟶ X) [IsAffineHom h]
      (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (V : X.FullAffineEtale) (s : G.obj.obj (op V.obj)),
      ((e h).hom.app G).hom.app (op ((U h).obj V))
          (((etaleSetPullback h).obj G).obj.map ((t h).hom.app V).op
            ((((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ h) (Type (u + 1))
          (X.smallGrothendieckTopology @Etale) (Y.smallGrothendieckTopology @Etale)).unit).app
          G).hom.app (op V.obj) s)) =
        ((a h).unit.app (((fullAffineEtaleInclusion X).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology X) X.smallEtaleTopology).obj G)).hom.app (op V) s) ∧
    ∃ (gamma : ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
        [IsAffineHom f] [IsAffineHom g], U f ⋙ U g ≅ U (g ≫ f))
      (c : ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
        [IsAffineHom f] [IsAffineHom g],
        etaleSetPullback f ⋙ etaleSetPullback g ≅ etaleSetPullback (g ≫ f))
      (d : ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
        [IsAffineHom f] [IsAffineHom g], L f ⋙ L g ≅ L (g ≫ f)),
    (∀ (X Y Z : Scheme.{u}) (f : Y ⟶ X) (g : Z ⟶ Y)
      [IsAffineHom f] [IsAffineHom g] (V : X.FullAffineEtale),
      (fullAffineEtaleInclusion Z).map ((gamma f g).hom.app V) ≫ (t (g ≫ f)).hom.app V =
        (t g).hom.app ((U f).obj V) ≫
          (MorphismProperty.Over.pullback @Etale ⊤ g).map ((t f).hom.app V) ≫
          (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).inv.app V.obj) ∧
    (∀ (X Y Z : Scheme.{u}) (f : Y ⟶ X) (g : Z ⟶ Y)
      [IsAffineHom f] [IsAffineHom g]
      (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
      (V : X.Etale) (s : G.obj.obj (op V)),
      ((c f g).hom.app G).hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj
          ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)))
        ((((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ g) (Type (u + 1))
          (Y.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).unit).app
          ((etaleSetPullback f).obj G)).hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V))
          ((((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
          (X.smallGrothendieckTopology @Etale) (Y.smallGrothendieckTopology @Etale)).unit).app
          G).hom.app (op V) s)) =
        ((etaleSetPullback (g ≫ f)).obj G).obj.map
          ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).inv.app V).op
          ((((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ (g ≫ f)) (Type (u + 1))
          (X.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)).unit).app
          G).hom.app (op V) s)) ∧
    (∀ (X Y Z : Scheme.{u}) (f : Y ⟶ X) (g : Z ⟶ Y)
      [IsAffineHom f] [IsAffineHom g]
      (F : Sheaf (fullAffineEtaleTopology X) (Type (u + 1)))
      (V : X.FullAffineEtale) (s : F.obj.obj (op V)),
      ((d f g).hom.app F).hom.app (op ((U g).obj ((U f).obj V)))
          (((a g).unit.app ((L f).obj F)).hom.app (op ((U f).obj V))
            (((a f).unit.app F).hom.app (op V) s)) =
        ((L (g ≫ f)).obj F).obj.map ((gamma f g).hom.app V).op
          (((a (g ≫ f)).unit.app F).hom.app (op V) s)) ∧
    (∀ (X Y Z : Scheme.{u}) (f : Y ⟶ X) (g : Z ⟶ Y)
      [IsAffineHom f] [IsAffineHom g]
      (G : Sheaf X.smallEtaleTopology (Type (u + 1))),
      ((fullAffineEtaleInclusion Z).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology Z) Z.smallEtaleTopology).map ((c f g).hom.app G) ≫
          (e (g ≫ f)).hom.app G =
        (e g).hom.app ((etaleSetPullback f).obj G) ≫
          (L g).map ((e f).hom.app G) ≫ (d f g).hom.app (((fullAffineEtaleInclusion
          X).sheafPushforwardContinuous (Type (u + 1))
          (fullAffineEtaleTopology X) X.smallEtaleTopology).obj G)) := by
  classical
  let U := fun {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h] ↦
    affineEtaleBaseChange h
  let t : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
      U h ⋙ fullAffineEtaleInclusion Y ≅
        fullAffineEtaleInclusion X ⋙ MorphismProperty.Over.pullback @Etale ⊤ h :=
    fun h ↦ Iso.refl _
  have hu : ∀ (X Y : Scheme.{u}) (h : Y ⟶ X) [IsAffineHom h],
      (U h).IsContinuous (fullAffineEtaleTopology X) (fullAffineEtaleTopology Y) :=
    fun X Y h ↦ (affineEtaleSiteBaseChange h).2.2.choose
  let L := fun {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h] ↦
    Functor.sheafPullbackConstruction.sheafPullback (U h) (Type (u + 1))
      (fullAffineEtaleTopology X) (fullAffineEtaleTopology Y)
  let a : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
      L h ⊣ (U h).sheafPushforwardContinuous (Type (u + 1))
        (fullAffineEtaleTopology X) (fullAffineEtaleTopology Y) :=
    fun h ↦ Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (U h) _ _ _
  obtain ⟨e, he⟩ := affineEtale_inverseImage_restriction_unit U t L a
  obtain ⟨c, hc, _⟩ := AlgebraicGeometry.etaleSetInverseImageCompositionUnits.2.2
  let c' := fun {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    [IsAffineHom f] [IsAffineHom g] ↦ c X Y Z f g
  obtain ⟨gamma, d, hgamma, hd, hcompat⟩ :=
    affineEtale_inverseImage_restriction_composition U t L a e he c'
      (fun X Y Z f g _ _ G V s ↦ hc X Y Z f g G V s)
  refine ⟨U, t, ?_, hu, L, a, e, ?_, he, gamma, c', d, hgamma, ?_, hd, hcompat⟩
  · intro X Y h _ V R hR
    exact (affineEtaleSiteBaseChange h).1 V R hR
  · intro X Y h _
    exact (affineEtaleSiteBaseChange h).2.2.choose_spec.2.1
  · intro X Y Z f g _ _ G V s
    exact hc X Y Z f g G V s

end AlgebraicGeometry.Scheme
