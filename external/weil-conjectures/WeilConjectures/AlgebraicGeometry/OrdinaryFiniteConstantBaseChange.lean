/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerSystem
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp
import WeilConjectures.AlgebraicGeometry.OrdinarySupportedUnitComparison

/-! # Base change of the ordinary constant-object unit

The equation holds for every commutative square; exchange need not be invertible.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, the substitution of
canonical pullback counits (auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace
  upperStar lowerStar DerivedCategory.singleFunctors
  ordinaryFiniteUnitPullback singleFunctorCompLeftDerivedUpperStarIso
  leftDerivedUpperStarComp derivedUpperStarLowerStarAdjunction derivedSquareUpperStarIso

private theorem unit_pullback_comp (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g fg hfg).hom.app
        (ordinaryFiniteUnit A Z) ≫
      (ordinaryFinitePullback A f).map (ordinaryFiniteUnitPullback A g).hom ≫
        (ordinaryFiniteUnitPullback A f).hom =
      (ordinaryFiniteUnitPullback A fg).hom := by
  exact ordinaryFiniteUnitPullback_comp A f g fg hfg

private theorem unit_pullback_square (A : Type (u + 1)) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {w : Y' ⟶ Y}
    (sq : CommSq v f' f w) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app
        (ordinaryFiniteUnit A Y) ≫
      (ordinaryFinitePullback A v).map (ordinaryFiniteUnitPullback A f).hom ≫
        (ordinaryFiniteUnitPullback A v).hom =
      (ordinaryFinitePullback A f').map (ordinaryFiniteUnitPullback A w).hom ≫
        (ordinaryFiniteUnitPullback A f').hom := by
  apply (cancel_epi
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f' w (v ≫ f) sq.w).hom.app
      (ordinaryFiniteUnit A Y))).mp
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [unit_pullback_comp, unit_pullback_comp]

private theorem mate_constant_unit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) {G : C ⥤ E} {H : D ⥤ F}
    (s : G ⋙ L₂ ⟶ L₁ ⋙ H)
    {K : C} {P : D} {K' : E} {P' : F}
    (a : L₁.obj K ⟶ P) (b : G.obj K ⟶ K') (c : H.obj P ⟶ P')
    (d : L₂.obj K' ⟶ P')
    (hc : s.app K ≫ H.map a ≫ c = L₂.map b ≫ d) :
    G.map (a₁.unit.app K ≫ R₁.map a) ≫
        (mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ s)).app P ≫ R₂.map c =
      b ≫ a₂.unit.app K' ≫ R₂.map d := by
  simp only [Functor.map_comp, Category.assoc]
  erw [((mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ s)).naturality_assoc a)]
  erw [reassoc_of% unit_mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ s) K]
  change a₂.unit.app (G.obj K) ≫ R₂.map (s.app K) ≫ R₂.map (H.map a) ≫ R₂.map c = _
  simp only [← Functor.map_comp, hc]
  rw [Functor.map_comp]
  exact a₂.unit_naturality_assoc b (R₂.map d)

/-- Exchange carries the constant-object adjunction unit to the constant-object
unit on the other side of any commutative square.

Source: blueprint latest, thm-amb-p1-adjunction.proof.md, substitution of canonical
pullback counits; the source-library constant-sheaf and single-object composition lemmas.
(auxiliary; not a blueprint node).

Proof: the ordinary constant-sheaf pullback comparison respects composition.
The derived single-object comparison takes this equality to the derived
pullback square. Expand the two constant-object units as adjunction units
followed by direct image of those comparisons. Naturality of exchange moves
the comparison past exchange, and the mate-unit identity replaces the pulled
unit followed by exchange by the new unit followed by the pullback square.
The comparison square then cancels, and unit naturality gives the formula.
No Cartesian, properness, finiteness, or nonemptiness hypothesis is needed. -/
theorem ordinaryFiniteConstant_baseChange (A : Type (u + 1)) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {w : Y' ⟶ Y}
    (sq : CommSq v f' f w) :
    (ordinaryFinitePullback A w).map (supportedDerivedUnit A f) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app (ordinaryFiniteUnit A X) ≫
        (ordinaryFinitePushforward A f').map (ordinaryFiniteUnitPullback A v).hom =
      (ordinaryFiniteUnitPullback A w).hom ≫ supportedDerivedUnit A f' := by
  rw [supportedDerivedUnit_eq_adjunction, supportedDerivedUnit_eq_adjunction]
  exact mate_constant_unit
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f')
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom
    (ordinaryFiniteUnitPullback A f).hom (ordinaryFiniteUnitPullback A w).hom
    (ordinaryFiniteUnitPullback A v).hom (ordinaryFiniteUnitPullback A f').hom
    (unit_pullback_square A sq)

end AlgebraicGeometry.Etale
