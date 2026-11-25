/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisons
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Kummer
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative

/-!
# Canonical arrows for the ordinary finite projective-line calculation

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/thm-amb-p1-decomposition.md and
thm-amb-p1-adjunction.md; Stacks Project, Tags 03PL and 03FD
(auxiliary; not a blueprint node).

## Main definitions

* `OrdinaryFiniteTwistTransport`: normalized roots and coefficient-line comparisons.
* `ordinaryFiniteP1Unit`, `ordinaryFiniteP1ChernPushforward`: decomposition components.
* `ordinaryFiniteProjection`: the specified ordered projection map.
* `ordinaryFiniteP1Right`: inverse image followed by the shifted twist.
* `ordinaryFiniteP1Exchange`, `ordinaryFiniteP1RightBaseChange`: base-change arrows.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor ChangeOfRings

namespace AlgebraicGeometry.Etale

attribute [local implicit_reducible] ordinaryFiniteSingleFunctor

-- Reuse the proposition instances already stored in the ordinary derived category.
-- This keeps the canonical localization data identical before taking object maps.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- Reuse the existing colimits of module sheaves once when elaborating unbounded
derived inverse images. This is the library's colimit structure, with no new assumption.
Source: the ordinary module derived categories in blueprint
proposition-adjunction-projective-line--1 (auxiliary; not a blueprint node). -/
instance ordinaryFiniteColimitsOfShapeInt (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) : HasColimitsOfShape ℤ
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  inferInstance

/-- The recorded derived inverse image, with its instances elaborated once.
Source: blueprint proposition-adjunction-projective-line--1
(auxiliary; not a blueprint node). -/
@[implicit_reducible]
def ordinaryFinitePullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X :=
  (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor

/-- The recorded unbounded derived direct image, with its instances elaborated once.
Source: blueprint proposition-adjunction-projective-line--1
(auxiliary; not a blueprint node). -/
@[implicit_reducible]
def ordinaryFinitePushforward (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategoryModule A X ⥤ DerivedCategoryModule A Y :=
  (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor

/-- The existing derived tensor, with its coefficient instances elaborated once.
Source: blueprint proposition-adjunction-projective-line--1
(auxiliary; not a blueprint node). -/
@[implicit_reducible]
def ordinaryFiniteTensor (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    DerivedCategoryModule A T ⥤ DerivedCategoryModule A T ⥤ DerivedCategoryModule A T :=
  derivedTensor (ModuleCat.{u + 1} A) T

/-- Normalized inverse-image comparisons for the concrete finite twist. The root
comparison is characterized by the inclusion into the units sheaf; the coefficient
comparison is characterized on pure tensors. Hence these are the canonical comparisons,
not an arbitrary system of twist isomorphisms.
Source: Stacks, Tags 03PK and 03Q1
(auxiliary; not a blueprint node). -/
structure OrdinaryFiniteTwistTransport (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) where
  roots : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsUnit (N : Γ(Y, ⊤)) →
    ((upperStar AddCommGrpCat.{u + 1} f).obj (Y.rootsOfUnitySheaf N) ≅
      X.rootsOfUnitySheaf N)
  line : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsUnit (N : Γ(Y, ⊤)) →
    ((upperStar (ModuleCat.{u + 1} A) f).obj (Scheme.finiteEtaleTateLine Y N A hA) ≅
      Scheme.finiteEtaleTateLine X N A hA)
  roots_normalization : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))),
    (upperStar AddCommGrpCat.{u + 1} f).map (kernel.ι (N • 𝟙 Y.gmSheaf)) ≫
        Scheme.upperStarGmSheafToGmSheaf f =
      (roots f hY).hom ≫ kernel.ι (N • 𝟙 X.gmSheaf)
  line_normalization : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤)))
      (W : Y.Etaleᵒᵖ) (a : A) (z : (Y.rootsOfUnitySheaf N).obj.obj W),
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
      (line f hY).hom).hom.app W (Scheme.finiteEtaleTateOneGenerator A N Y hA W a z) =
    Scheme.finiteEtaleTateOneGenerator A N X hA
      ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).op.obj W) a
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
        (roots f hY).hom).hom.app W z)

/-- The exact derived single-degree comparison, with the same cached embeddings.
Source: the exact inverse-image comparison with degree zero
(auxiliary; not a blueprint node). -/
def ordinaryFiniteSingleExactPullbackIso (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryFiniteSingleFunctor A Y ⋙
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ≅
      upperStar (ModuleCat.{u + 1} A) f ⋙ ordinaryFiniteSingleFunctor A X :=
  (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0

/-- The cached comparison is the canonical exact-derived single-degree comparison.
Source: the exact inverse-image comparison, blueprint proposition-adjunction-projective-line--1
(auxiliary; not a blueprint node). -/
theorem ordinaryFiniteSingleExactPullbackIso_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryFiniteSingleExactPullbackIso A f =
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0 := rfl

/-- The canonical single-degree comparison, transported along the cached embeddings.
Source: the exact inverse-image comparison with degree zero
(auxiliary; not a blueprint node). -/
def ordinaryFiniteSinglePullbackIso (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryFiniteSingleFunctor A Y ⋙ ordinaryFinitePullback A f ≅
      upperStar (ModuleCat.{u + 1} A) f ⋙ ordinaryFiniteSingleFunctor A X :=
  Functor.isoWhiskerLeft (ordinaryFiniteSingleFunctor A Y)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) ≪≫
    ordinaryFiniteSingleExactPullbackIso A f

/-- The canonical derived comparison on the shifted twist.
Source: blueprint lemma-cohomology-projective-line-trace
(auxiliary; not a blueprint node). -/
def ordinaryFiniteShiftedLinePullback (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (ordinaryFinitePullback A f).obj
        ((ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧) ≅
      (ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧ :=
  shiftedSinglePullbackIsoWith (ModuleCat.{u + 1} A) f
    (ordinaryFiniteSingleFunctor A Y) (ordinaryFiniteSingleFunctor A X)
    (ordinaryFiniteSinglePullbackIso A f)
    (Scheme.finiteEtaleTateLine Y N A hA) (Scheme.finiteEtaleTateLine X N A hA)
    (t.line f hY) 2

/-- The canonical comparison on the constant complex, with no chosen orientation.
Source: blueprint proposition-adjunction-projective-line--1
(auxiliary; not a blueprint node). -/
def ordinaryFiniteUnitPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ordinaryFinitePullback A f).obj (ordinaryFiniteUnit A Y) ≅
      ordinaryFiniteUnit A X :=
  (ordinaryFiniteSinglePullbackIso A f).app _ ≪≫
    (ordinaryFiniteSingleFunctor A X).mapIso
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app (ModuleCat.of A A))

/-- The unit comparison factors through the cached single-degree comparison.
Source: the canonical inverse-image comparison, blueprint proposition-adjunction-projective-line--1
(auxiliary; not a blueprint node). -/
theorem ordinaryFiniteUnitPullback_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ordinaryFiniteUnitPullback A f =
      (ordinaryFiniteSinglePullbackIso A f).app (ordinaryFiniteConstant A Y) ≪≫
        (ordinaryFiniteSingleFunctor A X).mapIso
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app
            (ModuleCat.of A A)) := rfl

/-- The shifted-line comparison uses the cached single-degree comparison and shift.
Source: the canonical shifted inverse-image comparison, blueprint
lemma-cohomology-projective-line-trace (auxiliary; not a blueprint node). -/
theorem ordinaryFiniteShiftedLinePullback_eq
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    letI : (ordinaryFinitePullback A f).CommShift ℤ :=
      commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
    ordinaryFiniteShiftedLinePullback A N hA t f hY =
      ((ordinaryFinitePullback A f).commShiftIso (2 : ℤ)).app
          ((ordinaryFiniteSingleFunctor A Y).obj (Scheme.finiteEtaleTateLine Y N A hA)) ≪≫
        (shiftFunctor (DerivedCategoryModule A X) (2 : ℤ)).mapIso
          ((ordinaryFiniteSinglePullbackIso A f).app (Scheme.finiteEtaleTateLine Y N A hA) ≪≫
            (ordinaryFiniteSingleFunctor A X).mapIso (t.line f hY)) := rfl

/-- The shifted twisted unit, the first component of the projective-line decomposition.
Source: blueprint lemma-cohomology-projective-line-trace
(auxiliary; not a blueprint node). -/
def ordinaryFiniteP1Unit (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    (ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⟶
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (ProjectiveLine S ↘ S)).unit.app _ ≫
    (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map
      (ordinaryFiniteShiftedLinePullback A N hA t (ProjectiveLine S ↘ S) hS).hom

/-- Push forward a degree-two Chern class using the actual inverse-image adjunction.
Source: blueprint lemma-cohomology-projective-line-trace
(auxiliary; not a blueprint node). -/
def ordinaryFiniteP1ChernPushforward (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u})
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) :
    ordinaryFiniteUnit A S ⟶
      (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
    (ProjectiveLine S ↘ S)).homEquiv _ _
      ((ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom ≫ c)

/-- The ordered projection map with the base coefficient first, exactly the
symmetry-conjugate of the adjoint-of-counit map used by the projection theorem.
Source: blueprint lemma-cohomology-projective-line-trace
(auxiliary; not a blueprint node). -/
def ordinaryFiniteProjection (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : DerivedCategoryModule A X)
    (K : DerivedCategoryModule A Y) :
    ((ordinaryFiniteTensor A Y).obj K).obj
        ((ordinaryFinitePushforward A f).obj L) ⟶
      (ordinaryFinitePushforward A f).obj
        (((ordinaryFiniteTensor A X).obj
          ((ordinaryFinitePullback A f).obj K)).obj L) :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app K).app _ ≫
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app L).app K ≫
      (ordinaryFinitePushforward A f).map
        (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app L).app _)

/-- Compose the recorded inverse image with tensoring by a specified source complex.
Source: blueprint proposition-adjunction-projective-line--1
(auxiliary; not a blueprint node). -/
def ordinaryFiniteTwistedPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (q : X ⟶ Y) (L : DerivedCategoryModule A X) :
    DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X :=
  ordinaryFinitePullback A q ⋙ derivedTensorRight (ModuleCat.{u + 1} A) X L

/-- The proposed right adjoint on the entire derived category.
Source: blueprint proposition-adjunction-projective-line--1
(auxiliary; not a blueprint node). -/
def ordinaryFiniteP1Right (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) :
    DerivedCategoryModule A S ⥤ DerivedCategoryModule A (ProjectiveLine S) :=
  ordinaryFiniteTwistedPullback A (ProjectiveLine S ↘ S)
    ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)

/-- Canonical proper exchange, expressed with the equivalent left-derived inverse images.
The middle arrow is exactly `exactDerivedBaseChangeMap` from the recorded dependency.
Source: Stacks, Tag 07A7 (auxiliary; not a blueprint node). -/
def ordinaryFiniteP1Exchange (A : Type (u + 1)) [CommRing A]
    {S' S : Scheme.{u}} (f : S' ⟶ S) (M : DerivedCategoryModule A (ProjectiveLine S)) :
    (ordinaryFinitePullback A f).obj
        ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj M) ⟶
      (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).obj
        ((ordinaryFinitePullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)).obj M) :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app _ ≫
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
      (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) f).toCommSq).app M ≫
      (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
          (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)).inv.app M)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Inverse-image composition around the projective-line base-change square.
Source: blueprint proposition-adjunction-projective-line--1, base-change normalization
(auxiliary; not a blueprint node). -/
def ordinaryFiniteP1PullbackSquare (A : Type (u + 1)) [CommRing A]
    {S' S : Scheme.{u}} (f : S' ⟶ S) (K : DerivedCategoryModule A S) :
    (ordinaryFinitePullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)).obj
      ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj K) ≅
    (ordinaryFinitePullback A (ProjectiveLine S' ↘ S')).obj
      ((ordinaryFinitePullback A f).obj K) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (ProjectiveSpace.map (ULift.{u} (Fin 2)) f) (ProjectiveLine S ↘ S)).symm.app K ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (ProjectiveLine S' ↘ S') f
      ((ProjectiveSpace.map (ULift.{u} (Fin 2)) f) ≫ (ProjectiveLine S ↘ S))
      (ProjectiveSpace.map_over (ULift.{u} (Fin 2)) f)).app K

/-- The tensor pullback comparison with its two input objects explicit.
Source: blueprint proposition-adjunction-projective-line--1, base-change normalization
(auxiliary; not a blueprint node). -/
def ordinaryFiniteTensorPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K L : DerivedCategoryModule A Y) :
    (ordinaryFinitePullback A f).obj ((derivedTensorRight (ModuleCat.{u + 1} A) Y L).obj K) ≅
      (derivedTensorRight (ModuleCat.{u + 1} A) X
        ((ordinaryFinitePullback A f).obj L)).obj ((ordinaryFinitePullback A f).obj K) :=
  (derivedTensorRightCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f L).app K

/-- Apply the canonical tensor bifunctor to an isomorphism in each factor.
Source: blueprint proposition-adjunction-projective-line--1, base-change normalization
(auxiliary; not a blueprint node). -/
def ordinaryFiniteTensorRightMapIso (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {K K' L L' : DerivedCategoryModule A T} (e : K ≅ K') (c : L ≅ L') :
    (derivedTensorRight (ModuleCat.{u + 1} A) T L).obj K ≅
      (derivedTensorRight (ModuleCat.{u + 1} A) T L').obj K' :=
  (derivedTensorRight (ModuleCat.{u + 1} A) T L).mapIso e ≪≫
    ((derivedTensorRightFunctor (ModuleCat.{u + 1} A) T).mapIso c).app K'

/-- Tensor pullback followed by specified comparisons of the two factors.
This constructs the comparison before specializing its schemes to projective lines.
Source: blueprint proposition-adjunction-projective-line--1, base-change normalization
(auxiliary; not a blueprint node). -/
def ordinaryFiniteTwistedPullbackComparison (A : Type (u + 1)) [CommRing A]
    {X Y X' Y' : Scheme.{u}} (q : X ⟶ Y) (q' : X' ⟶ Y') (f : Y' ⟶ Y) (g : X' ⟶ X)
    (L : DerivedCategoryModule A X) (L' : DerivedCategoryModule A X')
    (K : DerivedCategoryModule A Y)
    (e : (ordinaryFinitePullback A g).obj ((ordinaryFinitePullback A q).obj K) ≅
      (ordinaryFinitePullback A q').obj ((ordinaryFinitePullback A f).obj K))
    (c : (ordinaryFinitePullback A g).obj L ≅ L') :
    (ordinaryFinitePullback A g).obj ((ordinaryFiniteTwistedPullback A q L).obj K) ≅
      (ordinaryFiniteTwistedPullback A q' L').obj ((ordinaryFinitePullback A f).obj K) :=
  ordinaryFiniteTensorPullback A g ((ordinaryFinitePullback A q).obj K) L ≪≫
    ordinaryFiniteTensorRightMapIso A X' e c

/-- The canonical comparison `f_P⁻¹ G_q K ≅ G_q' f⁻¹ K`: tensor pullback, the
inverse-image square comparison, and the normalized finite-line comparison.
Source: blueprint proposition-adjunction-projective-line--1, base-change normalization
(auxiliary; not a blueprint node). -/
def ordinaryFiniteP1RightBaseChange (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S)
    (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤))) (K : DerivedCategoryModule A S) :
    (ordinaryFinitePullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)).obj
        ((ordinaryFiniteP1Right A N hA S).obj K) ≅
      (ordinaryFiniteP1Right A N hA S').obj
        ((ordinaryFinitePullback A f).obj K) :=
  ordinaryFiniteTwistedPullbackComparison A (ProjectiveLine S ↘ S)
    (ProjectiveLine S' ↘ S') f (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
    ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    ((ordinaryFiniteLine A N hA (ProjectiveLine S'))⟦(2 : ℤ)⟧) K
    (ordinaryFiniteP1PullbackSquare A f K)
    (ordinaryFiniteShiftedLinePullback A N hA t
      (ProjectiveSpace.map (ULift.{u} (Fin 2)) f) hP)

end AlgebraicGeometry.Etale
