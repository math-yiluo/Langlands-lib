/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic

/-! # The explicit proper-support Kunneth route

Source: blueprint latest, first triangle of thm-amb-p1-adjunction.proof.md.
This lower-level construction avoids the native RelativeMap module, whose definition
imports already depend on the coordinate extraction this route will prove.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem four_iso_inverse {D : Type v} [Category.{u} D]
    {X₀ X₁ X₂ X₃ X₄ : D} (i : X₀ ≅ X₁) (j : X₁ ≅ X₂)
    (k : X₂ ≅ X₃) (l : X₃ ≅ X₄) :
    (i ≪≫ j ≪≫ k ≪≫ l).inv = l.inv ≫ k.inv ≫ j.inv ≫ i.inv := by
  simp only [Iso.trans_inv, Category.assoc]

attribute [local instance high] SymmetricCategory.toBraidedCategory

section General

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]

/-- The component of the existing canonical derived tensor symmetry.
Source: Stacks Tag 06YU (auxiliary; not a blueprint node). -/
def supportedTensorSwapIso (Z : Scheme.{u})
    (M N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C)) :
    ((derivedTensor C Z).obj M).obj N ≅ ((derivedTensor C Z).obj N).obj M :=
  ((derivedTensorSymmetry C Z).app M).app N

@[reassoc]
theorem supportedTensorSwapIso_hom_naturality_left (Z : Scheme.{u})
    {M M' : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C)}
    (a : M ⟶ M') (N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C)) :
    ((derivedTensor C Z).map a).app N ≫ (supportedTensorSwapIso C Z M' N).hom =
      (supportedTensorSwapIso C Z M N).hom ≫ ((derivedTensor C Z).obj N).map a :=
  NatTrans.naturality_app (derivedTensorSymmetry C Z).hom N a

@[reassoc]
theorem supportedTensorSwapIso_inv_naturality_left (Z : Scheme.{u})
    {M M' : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C)}
    (a : M ⟶ M') (N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C)) :
    ((derivedTensor C Z).obj N).map a ≫ (supportedTensorSwapIso C Z M' N).inv =
      (supportedTensorSwapIso C Z M N).inv ≫ ((derivedTensor C Z).map a).app N := by
  simpa only [supportedTensorSwapIso, Iso.app_inv, Functor.flip_map_app,
    Functor.flip_obj_obj] using
    (NatTrans.naturality_app (derivedTensorSymmetry C Z).inv N a)

@[reassoc]
theorem supportedTensorSwapIso_inv_naturality_right (Z : Scheme.{u})
    (M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C))
    {N N' : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C)} (b : N ⟶ N') :
    ((derivedTensor C Z).map b).app M ≫ (supportedTensorSwapIso C Z M N').inv =
      (supportedTensorSwapIso C Z M N).inv ≫ ((derivedTensor C Z).obj M).map b := by
  simpa only [supportedTensorSwapIso, Iso.app_inv, Functor.flip_obj_map,
    Functor.flip_obj_obj] using
    ((derivedTensorSymmetry C Z).inv.app M).naturality b

end General

variable (A : Type (u + 1)) [CommRing A] [Finite A]

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- The specified compact-support compositor transported along an equality.
Source: the directComparison construction in the first triangle
(auxiliary; not a blueprint node). -/
def properRouteCompIso {W X S : Scheme.{u}} (p : W ⟶ X) (f : X ⟶ S)
    (h : W ⟶ S) (w : p ≫ f = h) [IsProper p] [IsProper f] [IsProper h] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) h ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) p ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) f :=
  (rightDerivedLowerShriekCongrIso A w).symm ≪≫ rightDerivedLowerShriekCompIso A p f

/-- A component of the specified compact-support projection isomorphism.
Source: the first triangle (auxiliary; not a blueprint node). -/
def properRouteProjection {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (E : DerivedCategoryModule A X) (M : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj E)).obj M ≅
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj E).obj
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj M)) :=
  haveI := isIso_projectionMap_of_finite A f
  (asIso ((projectionMap (ModuleCat.{u + 1} A) f).app E)).app M

theorem properRouteProjection_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (E : DerivedCategoryModule A X)
    (M : DerivedCategoryModule A Y) :
    (properRouteProjection A f E M).hom =
      ((projectionMap (ModuleCat.{u + 1} A) f).app E).app M := by
  rfl

/-- A component of canonical proper exchange, with its original chosen map.
Source: the first triangle (auxiliary; not a blueprint node). -/
def properRouteExchange {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) [IsProper f] [IsProper q]
    (E : DerivedCategoryModule A X) :
    (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj E) ≅
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).obj
        ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E) :=
  have := isIso_rightDerivedLowerShriekBaseChangeMap A sq
  (asIso (rightDerivedLowerShriekBaseChangeMap A sq)).app E

theorem properRouteExchange_hom {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) [IsProper f] [IsProper q]
    (E : DerivedCategoryModule A X) :
    (properRouteExchange A sq E).hom =
      (rightDerivedLowerShriekBaseChangeMap A sq).app E := by
  rfl

/-- Inverse projection, inverse exchange and the canonical swap.
Source: the coefficient extraction in the first triangle
(auxiliary; not a blueprint node). -/
def properSupportedKunnethInner {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) [IsProper f] [IsProper q]
    (E : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).obj
        (((derivedTensor (ModuleCat.{u + 1} A) W).obj
          ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E)).obj
            ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj K)) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).obj
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj E)) :=
  (properRouteProjection A q _ K).symm ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) Y).mapIso
      (properRouteExchange A sq E).symm).app K ≪≫
    supportedTensorSwapIso (ModuleCat.{u + 1} A) Y _ K

theorem properSupportedKunnethInner_inv {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) [IsProper f] [IsProper q]
    (E : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (properSupportedKunnethInner A sq E K).inv =
      (supportedTensorSwapIso (ModuleCat.{u + 1} A) Y
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj E)) K).inv ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        (properRouteExchange A sq E).hom).app K ≫
      (properRouteProjection A q
        ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E) K).hom := by
  simp only [properSupportedKunnethInner, Iso.trans_inv, Iso.symm_inv, Iso.app_inv,
    Functor.mapIso_inv, Category.assoc]

/-- The proper-support route: compositor, inner extraction, inverse projection and swap.
Source: the first triangle (auxiliary; not a blueprint node).
All data are constructed from the original maps; no Kunneth theorem is an input. -/
def properSupportedKunnethRoute {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) (h : W ⟶ S) (w : q ≫ g = h)
    [IsProper f] [IsProper g] [IsProper q] [IsProper h]
    (E : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) h).obj
        (((derivedTensor (ModuleCat.{u + 1} A) W).obj
          ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E)).obj
            ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj K)) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) S).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj E)).obj
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj K) :=
  (properRouteCompIso A q g h w).app _ ≪≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).mapIso
      (properSupportedKunnethInner A sq E K) ≪≫
    (properRouteProjection A g K _).symm ≪≫
    supportedTensorSwapIso (ModuleCat.{u + 1} A) S _ _

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensor rightDerivedLowerShriek properRouteProjection properRouteCompIso
  properSupportedKunnethInner supportedTensorSwapIso

/-- The inverse route in component form.
Source: the explicit route construction above
(auxiliary; not a blueprint node). -/
theorem properSupportedKunnethRoute_inv {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) (h : W ⟶ S) (w : q ≫ g = h)
    [IsProper f] [IsProper g] [IsProper q] [IsProper h]
    (E : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (properSupportedKunnethRoute A sq h w E K).inv =
      (supportedTensorSwapIso (ModuleCat.{u + 1} A) S
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj K)
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj E)).inv ≫
      (properRouteProjection A g K
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj E)).symm.inv ≫
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).mapIso
        (properSupportedKunnethInner A sq E K)).inv ≫
      ((properRouteCompIso A q g h w).app
        (((derivedTensor (ModuleCat.{u + 1} A) W).obj
          ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E)).obj
            ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj K))).inv := by
  exact four_iso_inverse _ _ _ _

end AlgebraicGeometry.Etale
