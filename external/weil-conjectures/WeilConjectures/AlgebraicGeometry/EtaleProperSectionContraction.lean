/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSupportedDiagonalUnit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.EtaleOrderedProjectionComparison
/-!
# Tensor contraction of a proper section integral

Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local implicit_reducible] ordinaryFiniteTwistedPullback derivedTensorRight
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
  conjugateIsoEquiv conjugateEquiv Adjunction.comp
  leftDerivedUpperStarCompSectionIso leftDerivedUpperStarComp
  derivedUpperStarLowerStarAdjunction

attribute [local instance 40000] Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 30000] Abelian.toPreadditive
attribute [local instance 21000] sheafBraidedCategory
attribute [local instance 20000] SymmetricCategory.toBraidedCategory
attribute [local instance] DerivedCategory.symmetricCategory'
attribute [local instance 20000] derivedBraidedCategory
attribute [local implicit_reducible] sheafMonoidalCategory sheafBraidedCategory

/-- The ordered section projection contracts against any normalized scalar integral.
Source: blueprint thm-amb-p1-adjunction.proof.md, tensoring a section integral.
(auxiliary; not a blueprint node).
Proof: apply the generic section integral tensor identity. Identify the conjugate
section unit with the derived section pushforward comparison. The ordered projection
comparison identifies each of its projection mates, and invertibility identifies their
inverses. The single-complex unitor equation then gives the stated contraction. -/
theorem properSection_contraction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (s : X ⟶ Y) (p : Y ⟶ X)
    [IsProper s] [IsProper p] (h : s ≫ p = 𝟙 X)
    (M : DerivedCategoryModule A X) (V : DerivedCategoryModule A Y)
    (δ : (ordinaryFinitePushforward A s).obj (ordinaryFiniteUnit A X) ⟶ V)
    (τ : (ordinaryFinitePushforward A p).obj V ⟶ ordinaryFiniteUnit A X) :
    let l := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h
    let a := derivedSectionPushIso (ModuleCat.{u + 1} A) s p h
    let q := CoordinateTrace.orderedProjectionIso A s
      ((ordinaryFinitePullback A p).obj M) (ordinaryFiniteUnit A X) ≪≫
        (ordinaryFinitePushforward A s).mapIso
          (((derivedTensor (ModuleCat.{u + 1} A) X).mapIso (l.app M)).app
            (ordinaryFiniteUnit A X) ≪≫ (singleUnitor A X).app M)
    a.hom.app (ordinaryFiniteUnit A X) ≫
        (ordinaryFinitePushforward A p).map δ ≫ τ = 𝟙 _ →
    a.hom.app M ≫ (ordinaryFinitePushforward A p).map q.inv ≫
        (ordinaryFinitePushforward A p).map
          (((ordinaryFiniteTensor A Y).obj ((ordinaryFinitePullback A p).obj M)).map δ) ≫
        (CoordinateTrace.orderedProjectionIso A p M V).inv ≫
        ((ordinaryFiniteTensor A X).obj M).map τ ≫ (singleUnitor A X).hom.app M = 𝟙 M := by
  intro l a q hi
  have : IsIso q.hom := by infer_instance
  have hp (E : DerivedCategoryModule A Y) :
      IsIso ((((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
        p).rightAdjointProjectionMap (T_C := (derivedTensor (ModuleCat.{u + 1} A) Y).flip)
        (T_D := (derivedTensor (ModuleCat.{u + 1} A) X).flip)
          ((flipFunctor _ _ _).map
            (canonicalPullbackTensorComparison (ModuleCat.{u + 1} A) p))).app E).app M) := by
    rw [orderedProjection_eq_symmetry]
    change IsIso (CoordinateTrace.orderedProjectionIso A p M E).hom
    infer_instance
  have hs : IsIso ((((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
    s).rightAdjointProjectionMap (T_C := (derivedTensor (ModuleCat.{u + 1} A) X).flip)
        (T_D := (derivedTensor (ModuleCat.{u + 1} A) Y).flip)
        ((flipFunctor _ _ _).map
          (canonicalPullbackTensorComparison (ModuleCat.{u + 1} A) s))).app
            (ordinaryFiniteUnit A X)).app ((ordinaryFinitePullback A p).obj M)) := by
    rw [orderedProjection_eq_symmetry]
    change IsIso (CoordinateTrace.orderedProjectionIso A s
      ((ordinaryFinitePullback A p).obj M) (ordinaryFiniteUnit A X)).hom
    infer_instance
  have hq' : IsIso
      ((((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s).rightAdjointProjectionMap
        (T_C := (derivedTensor (ModuleCat.{u + 1} A) X).flip)
        (T_D := (derivedTensor (ModuleCat.{u + 1} A) Y).flip)
          ((flipFunctor _ _ _).map
            (canonicalPullbackTensorComparison (ModuleCat.{u + 1} A) s))).app
              (ordinaryFiniteUnit A X)).app ((upperStar (ModuleCat.{u + 1} A)
                p).leftDerivedFunctor.obj M) ≫
        (lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctor.map
          (((derivedTensor (ModuleCat.{u + 1} A) X).map
            ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h).hom.app M)).app
              (ordinaryFiniteUnit A X) ≫
            ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
            (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X).hom ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X M).hom)) := by
    rw [orderedProjection_eq_symmetry]
    change IsIso q.hom
    infer_instance
  have ht := etaleSectionIntegralTensor (ModuleCat.{u + 1} A) s p h M
    (ordinaryFiniteUnit A X) (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X) V δ τ
  have hi' :
      (conjugateIsoEquiv
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s)) Adjunction.id
        (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h).symm).inv.app
          (ordinaryFiniteUnit A X) ≫
        (ordinaryFinitePushforward A p).map δ ≫ τ = 𝟙 _ := by
    simpa only [a, l, derivedSectionPushIso, conjugateIsoEquiv_apply_hom,
      conjugateIsoEquiv_apply_inv, Iso.symm_inv]
      using hi
  specialize ht hi'
  simp only [conjugateIsoEquiv_apply_inv, Iso.symm_inv, ← conjugateIsoEquiv_apply_hom] at ht
  have he : (singleUnitor A X).hom.app M =
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
            (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X).hom ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X M).hom :=
    derivedSingleUnitorNatIso_hom_app (ModuleCat.{u + 1} A) X M
  have hproj := orderedProjection_eq_symmetry (ModuleCat.{u + 1} A) p V M
  change _ = (CoordinateTrace.orderedProjectionIso A p M V).hom at hproj
  have hprojInv : inv
      ((((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).rightAdjointProjectionMap
        (T_C := (derivedTensor (ModuleCat.{u + 1} A) Y).flip)
        (T_D := (derivedTensor (ModuleCat.{u + 1} A) X).flip)
          ((flipFunctor _ _ _).map
            (canonicalPullbackTensorComparison (ModuleCat.{u + 1} A) p))).app V).app M) =
        (CoordinateTrace.orderedProjectionIso A p M V).inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [hproj, Iso.hom_inv_id]
  have hdiag := orderedProjection_eq_symmetry (ModuleCat.{u + 1} A) s
    (ordinaryFiniteUnit A X) ((ordinaryFinitePullback A p).obj M)
  change _ = (CoordinateTrace.orderedProjectionIso A s
    ((ordinaryFinitePullback A p).obj M) (ordinaryFiniteUnit A X)).hom at hdiag
  have hqhom :
      (((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s).rightAdjointProjectionMap
        (T_C := (derivedTensor (ModuleCat.{u + 1} A) X).flip)
        (T_D := (derivedTensor (ModuleCat.{u + 1} A) Y).flip)
        ((flipFunctor _ _ _).map
          (canonicalPullbackTensorComparison (ModuleCat.{u + 1} A) s))).app
            (ordinaryFiniteUnit A X)).app ((ordinaryFinitePullback A p).obj M) ≫
      (ordinaryFinitePushforward A s).map
        ((((derivedTensor (ModuleCat.{u + 1} A) X).map (l.hom.app M)).app
          (ordinaryFiniteUnit A X)) ≫
          ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
            (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X).hom ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X M).hom) =
        q.hom := by
    rw [hdiag]
    rfl
  have hqInv : inv
      ((((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) s).rightAdjointProjectionMap
        (T_C := (derivedTensor (ModuleCat.{u + 1} A) X).flip)
        (T_D := (derivedTensor (ModuleCat.{u + 1} A) Y).flip)
          ((flipFunctor _ _ _).map
            (canonicalPullbackTensorComparison (ModuleCat.{u + 1} A) s))).app
              (ordinaryFiniteUnit A X)).app ((upperStar (ModuleCat.{u + 1} A)
                p).leftDerivedFunctor.obj M) ≫
        (lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctor.map
          (((derivedTensor (ModuleCat.{u + 1} A) X).map
            ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) s p h).hom.app M)).app
              (ordinaryFiniteUnit A X) ≫
            ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
            (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X).hom ≫
          (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X M).hom)) = q.inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    dsimp only [l, ordinaryFinitePullback, ordinaryFinitePushforward] at hqhom
    rw [hqhom, Iso.hom_inv_id]
  simp only [hprojInv, hqInv] at ht
  dsimp only [ordinaryFinitePullback, ordinaryFinitePushforward,
    ordinaryFiniteTensor] at ht ⊢
  rw [he]
  dsimp only [a, l, derivedSectionPushIso, Functor.id_obj] at ht ⊢
  exact ht

end AlgebraicGeometry.Etale
