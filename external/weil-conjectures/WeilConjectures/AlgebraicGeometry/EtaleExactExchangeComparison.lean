/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.SectionProjectionUnit
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# The exact and resolution presentations of proper exchange -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
/-- The derived square is transported from the termwise exact square. -/
theorem derivedSquareUpperStarIso_eq_exact
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) :
    (derivedSquareUpperStarIso B sq).hom =
      Functor.whiskerLeft (upperStar B g).leftDerivedFunctor
        (leftDerivedUpperStarIsoMapDerivedCategory B f').hom ≫
      Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory B g).hom
        (upperStar B f').mapDerivedCategory ≫
      (exactDerivedSquareUpperStarIso B sq).hom ≫
      Functor.whiskerLeft (upperStar B f).mapDerivedCategory
        (leftDerivedUpperStarIsoMapDerivedCategory B g').inv ≫
      Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory B f).inv
        (upperStar B g').leftDerivedFunctor := by
  ext M
  simp only [derivedSquareUpperStarIso, exactDerivedSquareUpperStarIso,
    leftDerivedUpperStarComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp [Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    leftDerivedUpperStarIsoMapDerivedCategory, squareUpperStarIso, Category.assoc,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm]
/-- The inverse square component is the componentwise inverse compositor composite. -/
theorem derivedSquareUpperStarIso_inv_app
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    (derivedSquareUpperStarIso B sq).inv.app K =
      ((leftDerivedUpperStarComp B g' f).symm.app K ≪≫
        (leftDerivedUpperStarComp B f' g (g' ≫ f) sq.w).app K).hom := by
  rfl

/-- The canonical derived exchange is the transported exact exchange. -/
theorem derivedBaseChangeMap_eq_exact
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    (derivedBaseChangeMap B sq).app M =
      (leftDerivedUpperStarIsoMapDerivedCategory B g).hom.app
          ((lowerStar B f).rightDerivedFunctor.obj M) ≫
      (exactDerivedBaseChangeMap B sq).app M ≫
      (lowerStar B f').rightDerivedFunctor.map
        ((leftDerivedUpperStarIsoMapDerivedCategory B g').inv.app M) := by
  simp only [derivedBaseChangeMap, derivedBaseChangeSquare, exactDerivedBaseChangeMap,
    mateEquiv_apply, mapDerivedUpperStarLowerStarAdjunction_eq,
    Adjunction.ofNatIsoLeft_unit, Adjunction.ofNatIsoLeft_counit]
  rw [derivedSquareUpperStarIso_eq_exact]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]
  dsimp only [TwoSquare.mk, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Functor.comp_obj,
    Functor.comp_map]
  simp only [Category.id_comp]
  let R := (lowerStar B f').rightDerivedFunctor
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory B f').hom.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory B g).hom.app
      ((lowerStar B f).rightDerivedFunctor.obj M))
  erw [← R.map_comp_assoc, ← hn, R.map_comp,
    ← (derivedUpperStarLowerStarAdjunction B f').unit_naturality_assoc]
  have hm := (leftDerivedUpperStarIsoMapDerivedCategory B g').inv.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory B f).inv.app
      ((lowerStar B f).rightDerivedFunctor.obj M) ≫
        (derivedUpperStarLowerStarAdjunction B f).counit.app M)
  simp only [Functor.map_comp, Category.assoc] at hm
  change _ ≫ _ = _ ≫ _
  simp only [Category.assoc]
  erw [← R.map_comp_assoc]
  simp only [Functor.map_comp, Category.assoc]
  have hh := congrArg R.map hm.symm
  simp only [Functor.map_comp] at hh
  rw [reassoc_of% hh]
  dsimp only [R]
  erw [Category.id_comp, Category.comp_id]

end AlgebraicGeometry.Etale
