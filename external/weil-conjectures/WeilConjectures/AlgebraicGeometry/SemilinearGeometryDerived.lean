/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SemilinearGeometryCore

/-! # Normalized derived geometric operations on semilinear systems

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 07A4
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r c₂ v₂ k

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [ambientSmall : EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

section Geometry

variable (A : Data.{c, v, r} J B τ)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)

/-- Derived geometric operations with canonical K-injective and tensor normalizations.
Source: Zheng Construction 4.1 and Lemma 4.10 (auxiliary; not a blueprint node). -/
structure Geometry extends GeometryBase.{c, v, r} J B τ J' uInv uPush adjSet where
  /-- The same derived adjunction at each level. -/
  derivedLevelAdjunction : ∀ n : ℕ,
    (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules) ⊣ (levelPush n).rightDerivedFunctor
  /-- The level derived adjunction is the canonical localization of the actual
  ordinary module adjunction. This equality fixes its hom-equivalence, so a
  sign-twisted choice cannot satisfy the interface. -/
  derivedLevelAdjunction_canonical : ∀ n : ℕ,
    derivedLevelAdjunction n =
      (levelAdjunction n).mapDerivedCategoryRightDerivedAdjunction
  /-- The system derived adjunction is the canonical localization of the
  ordinary system adjunction. -/
  derivedAdjunction_canonical :
    adjunction = ordinaryAdjunction.mapDerivedCategoryRightDerivedAdjunction
  /-- Exact inverse image evaluation. -/
  pullEvaluation : ∀ n : ℕ,
    pull.mapDerivedCategory ⋙ e.{c, v, max c v r} J' coefficients coefficientTransition n ≅
      e.{c, v, max c v r} J B τ n ⋙ (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules)
  /-- Derived direct-image evaluation; no K-injective evaluation assumption is made. -/
  pushEvaluation : ∀ n : ℕ,
    push.rightDerivedFunctor ⋙ e.{c, v, max c v r} J B τ n ≅
      e.{c, v, max c v r} J' coefficients coefficientTransition n ⋙ (levelPush
        n).rightDerivedFunctor
  /-- The evaluation identifications respect the actual adjunction units. -/
  unit_evaluation : ∀ (n : ℕ) (M : DS.{c, v, max c v r} J B τ),
    (e.{c, v, max c v r} J B τ n).map (adjunction.unit.app M) ≫
        (pushEvaluation n).hom.app (pull.mapDerivedCategory.obj M) ≫
        (levelPush n).rightDerivedFunctor.map ((pullEvaluation n).hom.app M) =
      (derivedLevelAdjunction n).unit.app ((e.{c, v, max c v r} J B τ n).obj M)
  /-- The evaluation identifications respect the actual adjunction counits. -/
  counit_evaluation : ∀ (n : ℕ)
    (N : DS.{c, v, max c v r} J' coefficients coefficientTransition),
    (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules).map ((pushEvaluation n).hom.app N) ≫
        (derivedLevelAdjunction n).counit.app
          ((e.{c, v, max c v r} J' coefficients coefficientTransition n).obj N) =
      (pullEvaluation n).inv.app (push.rightDerivedFunctor.obj N) ≫
        (e.{c, v, max c v r} J' coefficients coefficientTransition n).map (adjunction.counit.app N)
  /-- The coefficient tensor/inverse-image comparison whose mate is b. -/
  coefficientPullback : ∀ {m n : ℕ} (h : n ≤ m),
    (Data.scalar.{c, v, r} A h).T ⋙
        ((derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules) :
          D.{c, v, max c v r} J (B n) ⥤ D.{c, v, max c v r} J' (coefficients n)) ≅
      ((derivedExact.{c, v, max c v r, c, v} J J' (B m)
          (coefficients m) (inverseImage m).modules) :
        D.{c, v, max c v r} J (B m) ⥤ D.{c, v, max c v r} J' (coefficients m)) ⋙
          (Data.scalar.{c, v, r} target h).T
  /-- The canonical tensor comparison for inverse image of systems. -/
  tensorPullback : A.closed.tensor ⋙ pull.mapDerivedCategory ≅
    (pull.mapDerivedCategory.prod pull.mapDerivedCategory) ⋙ target.closed.tensor

  /-- Tensor/inverse-image comparison at each actual coefficient level. -/
  levelTensorPullback : ∀ n : ℕ,
    (A.levelClosed n).tensor ⋙
        derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules ≅
      ((derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules).prod
        (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules)) ⋙ (target.levelClosed n).tensor
  /-- The tensor comparison evaluates to the specified level comparison. -/
  tensorPullback_evaluation : ∀ (n : ℕ) (M P : DS.{c, v, max c v r} J B τ),
    (e.{c, v, max c v r} J' coefficients coefficientTransition n).map
        (tensorPullback.hom.app (M, P)) ≫
        (target.tensorEvaluation n).hom.app
          (pull.mapDerivedCategory.obj M, pull.mapDerivedCategory.obj P) ≫
        (target.levelClosed n).tensor.map
          (Prod.mkHom ((pullEvaluation n).hom.app M) ((pullEvaluation n).hom.app P)) =
      (pullEvaluation n).hom.app (A.closed.tensor.obj (M, P)) ≫
        (derivedExact.{c, v, max c v r, c, v} J J' (B n)
          (coefficients n) (inverseImage n).modules).map
            ((A.tensorEvaluation n).hom.app (M, P)) ≫
        (levelTensorPullback n).hom.app
          ((e.{c, v, max c v r} J B τ n).obj M, (e.{c, v, max c v r} J B τ n).obj P)
  /-- The chosen ordinary realization acts as the identity on the actual
  component section carriers. This rules out twisting the evaluation by a sign. -/
  ordinaryPullEvaluation_sections : ∀ (n : ℕ) (M : Systems.{c, v, max c v r} J B τ)
    (U : C'ᵒᵖ)
    (x : ((evaluation.{c, v, max c v r} J' coefficients coefficientTransition n).obj
      (pull.obj M)).val.obj U),
    HEq ((((ordinaryPullEvaluation n).hom.app M).val.app U) x) x
  /-- Ordinary direct image has its actual componentwise realization. -/
  ordinaryPushEvaluation : ∀ n : ℕ,
    push ⋙ evaluation.{c, v, max c v r} J B τ n ≅ evaluation.{c, v, max c v r} J' coefficients
      coefficientTransition n ⋙ levelPush n
  /-- The ordinary push evaluation is the identity on the component carriers. -/
  ordinaryPushEvaluation_sections : ∀ (n : ℕ)
    (M : Systems.{c, v, max c v r} J' coefficients coefficientTransition) (U : Cᵒᵖ)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj (push.obj M)).val.obj U),
    HEq ((((ordinaryPushEvaluation n).hom.app M).val.app U) x) x
  /-- The ordinary system unit is the level unit under these realizations. -/
  ordinary_unit_evaluation : ∀ (n : ℕ) (M : Systems.{c, v, max c v r} J B τ),
    (evaluation.{c, v, max c v r} J B τ n).map (ordinaryAdjunction.unit.app M) ≫
      (ordinaryPushEvaluation n).hom.app (pull.obj M) ≫
      (levelPush n).map ((ordinaryPullEvaluation n).hom.app M) =
        (levelAdjunction n).unit.app ((evaluation.{c, v, max c v r} J B τ n).obj M)
  /-- On a K-injective target the derived Hom equivalence is the ordinary one. -/
  derivedLevel_transpose_model : ∀ (n : ℕ)
    (P : CochainComplex (Mod.{c, v, max c v r} J (B n)) ℤ)
    (I : CochainComplex (Mod.{c, v, max c v r} J' (coefficients n)) ℤ)
    [I.IsKInjective]
    (f : ((inverseImage n).modules.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
    ((derivedLevelAdjunction n).homEquiv _ _)
        ((Functor.mapDerivedCategoryFactors (inverseImage n).modules).hom.app P ≫
          DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
        ((((levelAdjunction n).mapHomologicalComplex (.up ℤ)).homEquiv P I) f) ≫
          ((levelPush n).rightDerivedFunctorObjQIso I).inv
  /-- The system derived adjunction is normalized before taking any evaluation. -/
  derived_transpose_model : ∀
    (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (I : CochainComplex (Systems.{c, v, max c v r} J' coefficients coefficientTransition) ℤ)
    [I.IsKInjective] (f : (pull.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
    (adjunction.homEquiv _ _)
        ((Functor.mapDerivedCategoryFactors pull).hom.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
        (((ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P I) f) ≫
          (push.rightDerivedFunctorObjQIso I).inv
  /-- Exact derived pull evaluation is the localization of its ordinary realization. -/
  pullEvaluation_model : ∀ n : ℕ,
    pullEvaluation n = Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso (ordinaryPullEvaluation n) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm
  /-- Restricting coefficient actions commutes with inverse image. -/
  restrictionPullback : ∀ {m n : ℕ} (h : n ≤ m),
    res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h) ⋙ (inverseImage m).modules ≅
      (inverseImage n).modules ⋙ res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J'
        coefficients coefficientTransition h)
  /-- The ordinary restriction comparison is the identity on the inverse-image
  underlying sheaf; this excludes an unrelated scalar or sign automorphism. -/
  restrictionPullback_underlying : ∀ {m n : ℕ} (h : n ≤ m)
    (M : Mod.{c, v, max c v r} J (B n)),
    (underlying.{c, v, r} J' (coefficients m)).map ((restrictionPullback h).hom.app M) ≫
      (inverseImage n).moduleUnderlying.hom.app M =
        (inverseImage m).moduleUnderlying.hom.app ((res.{c, v, max c v r} (coefficientMap.{c, v,
          max c v r} J B τ h)).obj M)
  /-- Termwise inverse image carries the horizontal transition of the actual
  system to the coefficient-restriction inverse image of that transition.
  This equation is imposed before taking complexes or localizing; specifying
  evaluation on component objects alone does not specify horizontal maps. -/
  ordinaryPullTransition : ∀ {m n : ℕ} (h : n ≤ m)
    (M : Systems.{c, v, max c v r} J B τ),
    (transition.{c, v, max c v r} J' coefficients coefficientTransition h).app (pull.obj M) ≫
        (res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J'
          coefficients coefficientTransition h)).map ((ordinaryPullEvaluation n).hom.app M) =
      (ordinaryPullEvaluation m).hom.app M ≫
        (inverseImage m).modules.map
          ((transition.{c, v, max c v r} J B τ h).app M) ≫
        (restrictionPullback h).hom.app ((evaluation.{c, v, max c v r} J B τ n).obj M)
  /-- Coefficient pullback is the scalar-adjunction transpose of the localized
  identity-on-underlying-sheaves restriction comparison. -/
  coefficientPullback_transpose : ∀ {m n : ℕ} (h : n ≤ m)
    (P : D.{c, v, max c v r} J (B m)),
    ((target.scalar h).adjunction.homEquiv _ _) ((coefficientPullback h).inv.app P) =
      (derivedExact.{c, v, max c v r, c, v} J J' (B m) (coefficients m) (inverseImage
        m).modules).map
        ((A.scalar h).adjunction.unit.app P) ≫
      ((Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso (restrictionPullback h) ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm).hom.app ((A.scalar h).T.obj P))
  /-- Level tensor pullback is fixed on the signed total K-flat representatives. -/
  levelTensorModel : ∀ n : ℕ,
    TensorComparisonModel.{c, v, r} J J' (B n) (coefficients n) (inverseImage n).modules
      (A.levelClosed n) (target.levelClosed n) (A.levelTensorModels n)
        (target.levelTensorModels n) (levelTensorPullback n)
  /-- Its ordinary maps are the inverse images of pure tensors. -/
  levelTensor_pure : ∀ n : ℕ,
    InverseTensorPure.{c, v, r} J J' uInv (B n) (coefficients n) (inverseImage n)
      (levelTensorModel n).ordinary
  /-- The system comparison is localized on the system category itself. -/
  tensorModel : TensorComparisonModel.{c, v, r} (coefficientSequenceTopology J)
    (coefficientSequenceTopology J') (systemRing.{c, v, max c v r} J B τ)
      (systemRing.{c, v, max c v r} J' coefficients coefficientTransition) pull A.closed
        target.closed
        A.tensorModels target.tensorModels tensorPullback
  /-- The ordinary system tensor map is fixed by ordinary, faithful evaluations. -/
  tensor_ordinary_evaluation : ∀ (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ),
    (evaluation.{c, v, max c v r} J' coefficients coefficientTransition n).map
      (tensorModel.ordinary M N).hom ≫
      (ordinaryEvaluationTensor.{c, v, r} J' coefficients coefficientTransition n (pull.obj M)
        (pull.obj N)).hom ≫
      ordinaryTensorHom.{c, v, r} J' (coefficients n)
        ((ordinaryPullEvaluation n).hom.app M) ((ordinaryPullEvaluation n).hom.app N) =
      (ordinaryPullEvaluation n).hom.app
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J
          B τ) M N) ≫
      (inverseImage n).modules.map (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom ≫
      ((levelTensorModel n).ordinary ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N)).hom

attribute [instance] GeometryBase.levelAdditive GeometryBase.levelLimits GeometryBase.levelColimits
  GeometryBase.levelPushAdditive GeometryBase.levelKInjective GeometryBase.pullAdditive
  GeometryBase.pullLimits GeometryBase.pullColimits GeometryBase.pushAdditive
  GeometryBase.systemKInjective

end Geometry
end WeilConjectures.SemilinearSections
