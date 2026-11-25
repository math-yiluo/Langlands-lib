/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
/-! # Pullback of the inverse right unit with constant degree-zero coefficients

Source: monoidal inverse-image coherence, Stacks Tag 06YU; the right-unit step of
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u uB
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
private theorem unit_pairing
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (S : C ⥤ C) (T : D ⥤ D)
    (UY IY : C) (UX IX : D) (K : C)
    (uy : UY ≅ IY) (ux : UX ≅ IX) (e : F.obj IY ≅ IX) (u : F.obj UY ≅ UX)
    (ry : S.obj IY ≅ K) (rx : T.obj IX ≅ F.obj K)
    (du : F.obj (S.obj UY) ⟶ T.obj (F.obj UY))
    (di : F.obj (S.obj IY) ⟶ T.obj (F.obj IY))
    (hn : F.map (S.map uy.inv) ≫ du = di ≫ T.map (F.map uy.inv))
    (hu : F.map uy.inv ≫ u.hom = e.hom ≫ ux.inv)
    (hr : di ≫ T.map e.hom ≫ rx.hom = F.map ry.hom) :
    F.map (ry.inv ≫ S.map uy.inv) ≫ du ≫ T.map u.hom =
      rx.inv ≫ T.map ux.inv := by
  have hi : F.map ry.inv ≫ di ≫ T.map e.hom = rx.inv := by
    apply (cancel_mono rx.hom).1
    simp only [Category.assoc, Iso.inv_hom_id]
    rw [hr, ← F.map_comp, Iso.inv_hom_id, F.map_id]
  rw [F.map_comp, Category.assoc, ← Category.assoc (F.map (S.map uy.inv)), hn]
  simp only [Category.assoc]
  rw [← T.map_comp, hu, T.map_comp]
  simpa only [Category.assoc] using congrArg (fun a ↦ a ≫ T.map ux.inv) hi

private theorem constant_iso_eq
    (B : Type uB) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (M : B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (genericConstantIso B M f).hom =
      (leftDerivedUpperStarSingleConstantSheafIso B f M).hom := by
  simp only [genericConstantIso, leftDerivedUpperStarSingleConstantSheafIso,
    singleFunctorCompLeftDerivedUpperStarIso, Functor.singleFunctorCompLeftDerivedFunctorIso,
    Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.assoc, leftDerivedUpperStarIsoMapDerivedCategory,
    constantSingle]

private noncomputable def constant_unit_iso
    (B : Type uB) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) (K : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    ((derivedTensor B X).obj K).obj (constantSingle B X (𝟙_ B)) ≅ K :=
  ((derivedTensor B X).obj K).mapIso (singleFunctorObjUnitIso B X) ≪≫
    derivedTensorRightUnitor B X K

private theorem generic_unit
    (B : Type uB) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    (upperStar B f).leftDerivedFunctor.map (constant_unit_iso B Y K).inv ≫
      ((leftDerivedUpperStarTensorComparison B f).app K).app (constantSingle B Y (𝟙_ B)) ≫
      ((derivedTensor B X).obj ((upperStar B f).leftDerivedFunctor.obj K)).map
        (genericConstantIso B (𝟙_ B) f).hom =
      (constant_unit_iso B X ((upperStar B f).leftDerivedFunctor.obj K)).inv := by
  have hu := leftDerivedUpperStar_map_singleFunctorObjUnitIso_inv_comp B f
  rw [← constant_iso_eq] at hu
  dsimp only [constant_unit_iso, Iso.trans, Functor.mapIso]
  exact unit_pairing (upperStar B f).leftDerivedFunctor ((derivedTensor B Y).obj K)
    ((derivedTensor B X).obj ((upperStar B f).leftDerivedFunctor.obj K))
    (constantSingle B Y (𝟙_ B)) _ (constantSingle B X (𝟙_ B)) _ K
    (singleFunctorObjUnitIso B Y) (singleFunctorObjUnitIso B X)
    (leftDerivedUpperStarUnitIso B f) (genericConstantIso B (𝟙_ B) f)
    (derivedTensorRightUnitor B Y K) (derivedTensorRightUnitor B X _) _ _
    (((leftDerivedUpperStarTensorComparison B f).app K).naturality
      (singleFunctorObjUnitIso B Y).inv) hu
    (leftDerivedUpperStarTensorComparison_rightUnitor_hom B f K)

/-- The prescribed constant-object comparison preserves the inverse right-unit map.

Source: Stacks Tag 06YU and the unit step of the finite-twist evaluation argument
(auxiliary; not a blueprint node).

Proof: identify the constant degree-zero complex with the derived monoidal unit.
The single/pullback comparison is the exact-functor comparison; at the coefficient unit
its composite with constant pullback is the monoidal unit comparison. Naturality of the
tensor comparison in this unit identification reduces the assertion to oplax right
unitality. Postcomposition with the right-unitor isomorphism then gives its inverse
version. All objects and pullbacks are arbitrary, including zero coefficients and
empty schemes. -/
theorem ordinaryFiniteDerivedRightUnit_pullback
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ K : DerivedCategoryModule A Y,
      (ordinaryFinitePullback A f).map (derivedTensorSingleUnitIso K).inv ≫
        ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app K).app
          (ordinaryFiniteUnit A Y) ≫
        ((ordinaryFiniteTensor A X).obj ((ordinaryFinitePullback A f).obj K)).map
          (ordinaryFiniteUnitPullback A f).hom =
      (derivedTensorSingleUnitIso ((ordinaryFinitePullback A f).obj K)).inv) := by
  intro K
  change (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
    (constant_unit_iso (ModuleCat.{u + 1} A) Y K).inv ≫ _ =
      (constant_unit_iso (ModuleCat.{u + 1} A) X
        ((ordinaryFinitePullback A f).obj K)).inv
  exact generic_unit (ModuleCat.{u + 1} A) f K

end AlgebraicGeometry.Etale
