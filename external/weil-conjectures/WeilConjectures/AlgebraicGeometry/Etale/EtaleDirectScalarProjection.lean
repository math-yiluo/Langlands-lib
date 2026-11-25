/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.AlgebraicGeometry.Tensor.TensorProjectionAdjunct
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorCoherence

/-! # Scalar compatibility of the ordered direct-image projection -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Functor
private def curryComparison
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (F : C ⥤ D)
    (d : Functor.uncurry.obj T ⋙ F ⟶ F.prod F ⋙ Functor.uncurry.obj U) :
    (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj U where
  app K :=
    { app := fun L ↦ d.app (K, L)
      naturality := fun L L' f ↦ by
        change F.map ((T.obj K).map f) ≫ d.app (K, L') =
          d.app (K, L) ≫ (U.obj (F.obj K)).map (F.map f)
        have h := d.naturality (show (K, L) ⟶ (K, L') from (𝟙 K, f))
        simpa only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
          Functor.uncurry_obj_map, _root_.CategoryTheory.Functor.map_id, NatTrans.id_app,
          Category.id_comp] using h }
  naturality K K' f := by
    ext L
    change F.map ((T.map f).app L) ≫ d.app (K', L) =
      d.app (K, L) ≫ (U.map (F.map f)).app (F.obj L)
    have h := d.naturality (show (K, L) ⟶ (K', L) from (f, 𝟙 L))
    simpa only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
      Functor.uncurry_obj_map, _root_.CategoryTheory.Functor.map_id, Category.comp_id] using h

namespace AlgebraicGeometry.Etale

/-- The ordered counit projection as a natural transformation in the input object.
Source: Stacks 0GL6, counit projection formula
(blueprint: lem-pur-etale-direct-scalar-projection).
It is a composite of the source symmetry, the flipped counit projection, and the
image of the target symmetry, so its naturality is inherited from these maps. -/
@[irreducible] def orderedDirectProjectionNat (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (K : DerivedCategoryModule R Y) :
    (lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor ⋙
        (derivedTensor (ModuleCat.{u + 1} R) Y).obj K ⟶
      (derivedTensor (ModuleCat.{u + 1} R) X).obj
          ((upperStar (ModuleCat.{u + 1} R) p).leftDerivedFunctor.obj K) ⋙
        (lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor :=
  Functor.whiskerLeft (lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor
      ((derivedTensorSymmetry (ModuleCat.{u + 1} R) Y).hom.app K) ≫
    (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R) p).flipApp K ≫
    Functor.whiskerRight
      ((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.flipApp
        ((upperStar (ModuleCat.{u + 1} R) p).leftDerivedFunctor.obj K))
      (lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor

/-- The counit projection, with the base coefficient first.
Source: Stacks 0GL6, projection formula preceding change of rings
(blueprint: lem-pur-etale-direct-scalar-projection). -/
@[irreducible] def orderedDirectProjection (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategoryModule R Y) (E : DerivedCategoryModule R X) :
    ((derivedTensor (ModuleCat.{u + 1} R) Y).obj K).obj
        ((lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor.obj E) ⟶
      (lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor.obj
        (((derivedTensor (ModuleCat.{u + 1} R) X).obj
          ((upperStar (ModuleCat.{u + 1} R) p).leftDerivedFunctor.obj K)).obj E) :=
  (orderedDirectProjectionNat R p K).app E

/-- The component formula for the structured ordered projection.
Source: Stacks 0GL6, counit projection formula
(blueprint: lem-pur-etale-direct-scalar-projection). -/
theorem orderedDirectProjection_eq (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategoryModule R Y) (E : DerivedCategoryModule R X) :
    orderedDirectProjection R p K E =
      ((derivedTensorSymmetry (ModuleCat.{u + 1} R) Y).hom.app K).app
          ((lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor.obj E) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R) p).app E).app K ≫
        (lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor.map
          (((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app E).app
            ((upperStar (ModuleCat.{u + 1} R) p).leftDerivedFunctor.obj K)) := by
  unfold orderedDirectProjection orderedDirectProjectionNat
  rfl

private theorem orderedDirectProjection_flip
    (R : Type (u + 1)) [CommRing R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategoryModule R Y) (E : DerivedCategoryModule R X) :
    orderedDirectProjection R p K E =
      (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).rightAdjointProjectionMap
        (T_C := (derivedTensor (ModuleCat.{u + 1} R) X).flip)
        (T_D := (derivedTensor (ModuleCat.{u + 1} R) Y).flip)
          ((flipFunctor _ _ _).map
            (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} R) p))).app E).app K := by
  rw [Adjunction.rightAdjointProjectionMap_app_app]
  apply Equiv.injective
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p).homEquiv _ _).symm
  simp only [Functor.flip_obj_obj, Functor.id_obj]
  rw [Equiv.symm_apply_apply, orderedDirectProjection_eq]
  have h := tensorProjectionAdjunct R p K
    ((lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor.obj E) E (𝟙 _)
  simpa only [_root_.CategoryTheory.Functor.map_id, Category.id_comp,
    flipFunctor_map_app_app, Functor.flip_map_app] using h

/-- The scalar mate intertwines the two ordered counit projections.
Source: Stacks 0GL6 and 07A4; compact-scalar coherence proof step 2, proper part.
(blueprint: lem-pur-etale-direct-scalar-projection).
Proof: apply the B-geometric adjunction's Hom equivalence to both composites.
The mate counit identity replaces the pullback of scalarMate followed by counit
by scalarPullbackIso followed by scalar extension of the A-counit. Naturality
moves the tensor comparisons past that counit. The binary scalar/pullback tensor
square identifies the remaining composites. This is the identity-topos coefficient
specialization of ringed exchange/tensor coherence. Conjugate by the canonical
signed tensor symmetries on source and target to put the coefficient first.
Scalar tensor comparison respects these symmetries: on homogeneous K-flat
representatives both paths have sign (-1)^(pq), and localization descends that
identity. The argument applies to every morphism and every unbounded input;
properness and finite coefficients are unnecessary. -/
theorem etaleDirectScalarProjection
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K : DerivedCategoryModule A Y) (E : DerivedCategoryModule A X) :
    (scalarExtension φ Y).map (orderedDirectProjection A p K E) ≫
      (scalarMate φ p).app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj K)).obj E) ≫
      (lowerStar (ModuleCat.{u + 1} B) p).rightDerivedFunctor.map
        ((ExceptionalCoefficients.tensorIso φ X).hom.app
            ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj K, E) ≫
          ((derivedTensor (ModuleCat.{u + 1} B) X).map
            ((scalarPullbackIso φ p).inv.app K)).app ((scalarExtension φ X).obj E)) =
    (ExceptionalCoefficients.tensorIso φ Y).hom.app
        (K, (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj E) ≫
      ((derivedTensor (ModuleCat.{u + 1} B) Y).obj
        ((scalarExtension φ Y).obj K)).map ((scalarMate φ p).app E) ≫
      orderedDirectProjection B p ((scalarExtension φ Y).obj K)
        ((scalarExtension φ X).obj E) := by
  let QA := scalarExtension φ Y
  let QX := scalarExtension φ X
  let LA := (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor
  let LB := (upperStar (ModuleCat.{u + 1} B) p).leftDerivedFunctor
  let RB := (lowerStar (ModuleCat.{u + 1} B) p).rightDerivedFunctor
  let TA := derivedTensor (ModuleCat.{u + 1} A) Y
  let TB := derivedTensor (ModuleCat.{u + 1} B) Y
  let UA := derivedTensor (ModuleCat.{u + 1} A) X
  let UB := derivedTensor (ModuleCat.{u + 1} B) X
  let a := scalarPullbackIso φ p
  let dY := curryComparison TA TB QA (ExceptionalCoefficients.tensorIso φ Y).hom
  let dX := curryComparison UA UB QX (ExceptionalCoefficients.tensorIso φ X).hom
  have hc (P Q : DerivedCategoryModule A Y) :
      LB.map ((dY.app Q).app P) ≫
        ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} B) p).app
          (QA.obj Q)).app (QA.obj P) ≫
        (UB.obj (LB.obj (QA.obj Q))).map (a.hom.app P) ≫
        (UB.map (a.hom.app Q)).app (QX.obj (LA.obj P)) =
      a.hom.app ((TA.obj Q).obj P) ≫
        QX.map (((leftDerivedUpperStarTensorComparison
          (ModuleCat.{u + 1} A) p).app Q).app P) ≫
        (dX.app (LA.obj Q)).app (LA.obj P) := by
    simpa only [dY, dX, QA, QX, LA, LB, TA, UB, a,
      MonoidalCategory.tensorHom_def', curryComparison,
      leftDerivedUpperStarTensorIso_hom, Category.assoc,
      MonoidalCategory.curriedTensor_map_app, MonoidalCategory.curriedTensor_obj_map,
      derivedTensor, Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
      Functor.postcompose₂_obj_obj_obj_obj, MonoidalCategory.curriedTensor_obj_obj]
      using (etaleScalarPullback_tensor φ p Q P).symm
  have hm := Adjunction.rightAdjointProjectionMap_mate
    (T₁ := UA.flip) (S₁ := TA.flip) (T₂ := UB.flip) (S₂ := TB.flip)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p)
    ((flipFunctor _ _ _).map
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) p))
    ((flipFunctor _ _ _).map
      (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} B) p))
    ((flipFunctor _ _ _).map dY) ((flipFunctor _ _ _).map dX)
    a.hom (scalarMate φ p) hc
    (fun M ↦ mateEquiv_counit
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p)
      (TwoSquare.mk _ _ _ _ a.hom) M) E K
  rw [orderedDirectProjection_flip, orderedDirectProjection_flip]
  apply (cancel_mono (RB.map ((UB.map (a.hom.app K)).app (QX.obj E)))).1
  simp only [Functor.map_comp, Category.assoc]
  rw [← RB.map_comp]
  simpa only [dY, dX, QA, QX, LA, LB, RB, TA, TB, UA, UB, a,
    curryComparison, flipFunctor_map_app_app, Functor.flip_map_app,
    Functor.flip_obj_map, Functor.flip_obj_obj, ← NatTrans.comp_app,
    ← Functor.map_comp, Iso.inv_hom_id_app, Iso.inv_hom_id,
    _root_.CategoryTheory.Functor.map_id, NatTrans.id_app, Functor.comp_obj,
    Functor.prod_obj, Functor.uncurry_obj_obj, Category.comp_id, Category.assoc] using hm

end AlgebraicGeometry.Etale
