/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSupportedDiagonalUnit
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteSingleUnitNormalization
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceContractions
import WeilConjectures.AlgebraicGeometry.EtaleDiagonalSectionIntegral
import WeilConjectures.AlgebraicGeometry.EtaleDiagonalTriangles
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCounitCoefficient
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceEvaluationNormalization
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# Triangles from the scalar coordinate integrals, with coefficient transport
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local implicit_reducible] constantComplex in
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar in
private theorem scalarFirstTriangle
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hJ : Scheme.IsLisseRankOneSheaf J) (d : ℤ)
    (t₀ : (ordinaryFinitePushforward A f).obj
      ((ordinaryFinitePullback A f).obj (CoordinateTrace.shiftedLine A J d)) ⟶
        constantComplex A Y)
    (δ : (ordinaryFinitePushforward A (pullback.diagonal f)).obj (ordinaryFiniteUnit A X) ⟶
      (ordinaryFinitePullback A (pullback.snd f f)).obj
        ((ordinaryFinitePullback A f).obj (CoordinateTrace.shiftedLine A J d)))
    (t₁ : (ordinaryFinitePushforward A (pullback.fst f f)).obj
      ((ordinaryFinitePullback A (pullback.snd f f)).obj
        ((ordinaryFinitePullback A f).obj (CoordinateTrace.shiftedLine A J d))) ⟶
          constantComplex A X)
    (t₂ : (ordinaryFinitePushforward A (pullback.snd f f)).obj
      ((ordinaryFinitePullback A (pullback.snd f f)).obj
        ((ordinaryFinitePullback A f).obj (CoordinateTrace.shiftedLine A J d))) ⟶
          constantComplex A X)
    (ht₁ : (CoordinateTrace.exchange1 A f
      ((ordinaryFinitePullback A f).obj (CoordinateTrace.shiftedLine A J d))).hom ≫ t₁ =
        (ordinaryFinitePullback A f).map t₀ ≫
          (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom)
    (ht₂ : (CoordinateTrace.exchange2 A f
      ((ordinaryFinitePullback A f).obj (CoordinateTrace.shiftedLine A J d))).hom ≫
        (ordinaryFinitePushforward A (pullback.snd f f)).map
          (CoordinateTrace.coordinate A f (CoordinateTrace.shiftedLine A J d)).hom ≫ t₂ =
        (ordinaryFinitePullback A f).map t₀ ≫
          (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom)
    (hi₁ : (diagonalFirstPushSection A f).hom.app (ordinaryFiniteUnit A X) ≫
      (ordinaryFinitePushforward A (pullback.fst f f)).map δ ≫ t₁ ≫
        (ordinaryFiniteSingleUnitIso A X).inv = 𝟙 _) :
    ∀ M : DerivedCategoryModule A X,
      (ordinaryFinitePushforward A f).map
          (Adjunction.unitComponent (ordinaryFinitePushforward A f)
            (CoordinateTrace.H A f (CoordinateTrace.shiftedLine A J d))
            (supportedDiagonalUnit A f (CoordinateTrace.shiftedLine A J d) δ) M) ≫
        CoordinateTrace.evaluation A f (CoordinateTrace.shiftedLine A J d) t₀
          ((ordinaryFinitePushforward A f).obj M) = 𝟙 _ := by
  intro M
  exact supportedDiagonalUnit_first A f (CoordinateTrace.shiftedLine A J d) δ t₀ t₁
    (CoordinateTrace.contractions A f J hJ d t₀ t₁ t₂ ht₁ ht₂).1
    (diagonalFirstTensorIntegral A f (CoordinateTrace.shiftedLine A J d) δ t₁ hi₁) M

attribute [local instance 20000] SymmetricCategory.toBraidedCategory
attribute [local implicit_reducible] constantComplex constantSheaf
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
attribute [local implicit_reducible] sheafMonoidalCategory sheafBraidedCategory derivedTensorRight
  ordinaryFiniteTwistedPullback CoordinateTrace.H
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
  singleFunctorObjUnitIso derivedTensorRightUnitor
  conjugateIsoEquiv conjugateEquiv Adjunction.comp
  leftDerivedUpperStarCompSectionIso leftDerivedUpperStarComp
  derivedUpperStarLowerStarAdjunction

/-- Scalar coordinate traces and their two diagonal integrals imply the transported
triangles for the prescribed trace counit.
Source: blueprint thm-amb-p1-adjunction.proof.md, the two triangle calculations.
(auxiliary; not a blueprint node).
Proof: apply the even-line coordinate contraction theorem to the two exchange
identities. Tensor the first scalar section integral by the section projection law.
The generic supported-diagonal calculations give both triangles for coordinate
evaluation. The coefficient naturality square and the trace/evaluation comparison
identify evaluation with the counit transported along the supplied coefficient
isomorphism. Transport the two triangles along this isomorphism. -/
theorem evenLineDiagonalUnit_triangles
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    [IsLocallyNoetherian X] [CompactSpace X] [IsLocallyNoetherian Y] [CompactSpace Y]
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hJ : Scheme.IsLisseRankOneSheaf J) (d : ℤ)
    (L' : DerivedCategoryModule A X)
    (w : (ordinaryFinitePullback A f).obj (CoordinateTrace.shiftedLine A J d) ≅ L')
    (τ : (ordinaryFinitePushforward A f).obj L' ⟶ ordinaryFiniteUnit A Y)
    (t₀ : (ordinaryFinitePushforward A f).obj
      ((ordinaryFinitePullback A f).obj (CoordinateTrace.shiftedLine A J d)) ⟶
        constantComplex A Y)
    (ht₀ : t₀ = (ordinaryFinitePushforward A f).map w.hom ≫ τ ≫
      (ordinaryFiniteSingleUnitIso A Y).hom)
    (δ : (ordinaryFinitePushforward A (pullback.diagonal f)).obj (ordinaryFiniteUnit A X) ⟶
      (ordinaryFinitePullback A (pullback.snd f f)).obj
        ((ordinaryFinitePullback A f).obj (CoordinateTrace.shiftedLine A J d)))
    (t₁ : (ordinaryFinitePushforward A (pullback.fst f f)).obj
      ((ordinaryFinitePullback A (pullback.snd f f)).obj
        ((ordinaryFinitePullback A f).obj (CoordinateTrace.shiftedLine A J d))) ⟶
          constantComplex A X)
    (t₂ : (ordinaryFinitePushforward A (pullback.snd f f)).obj
      ((ordinaryFinitePullback A (pullback.snd f f)).obj
        ((ordinaryFinitePullback A f).obj (CoordinateTrace.shiftedLine A J d))) ⟶
          constantComplex A X)
    (ht₁ : (CoordinateTrace.exchange1 A f
      ((ordinaryFinitePullback A f).obj (CoordinateTrace.shiftedLine A J d))).hom ≫ t₁ =
        (ordinaryFinitePullback A f).map t₀ ≫
          (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom)
    (ht₂ : (CoordinateTrace.exchange2 A f
      ((ordinaryFinitePullback A f).obj (CoordinateTrace.shiftedLine A J d))).hom ≫
        (ordinaryFinitePushforward A (pullback.snd f f)).map
          (CoordinateTrace.coordinate A f (CoordinateTrace.shiftedLine A J d)).hom ≫ t₂ =
        (ordinaryFinitePullback A f).map t₀ ≫
          (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom)
    (hi₁ : (diagonalFirstPushSection A f).hom.app (ordinaryFiniteUnit A X) ≫
      (ordinaryFinitePushforward A (pullback.fst f f)).map δ ≫ t₁ ≫
        (ordinaryFiniteSingleUnitIso A X).inv = 𝟙 _)
    (hi₂ : (diagonalPushSection A f).hom.app (ordinaryFiniteUnit A X) ≫
      (ordinaryFinitePushforward A (pullback.snd f f)).map δ ≫ t₂ ≫
        (ordinaryFiniteSingleUnitIso A X).inv = 𝟙 _) :
    ∃ η : 𝟭 (DerivedCategoryModule A X) ⟶
        ordinaryFinitePushforward A f ⋙ ordinaryFiniteTwistedPullback A f L',
      (∀ M : DerivedCategoryModule A X,
        (ordinaryFinitePushforward A f).map (η.app M) ≫
          (ordinaryFiniteTraceCounit A f L' τ).app
            ((ordinaryFinitePushforward A f).obj M) = 𝟙 _) ∧
      (∀ K : DerivedCategoryModule A Y,
        η.app ((ordinaryFiniteTwistedPullback A f L').obj K) ≫
          (ordinaryFiniteTwistedPullback A f L').map
            ((ordinaryFiniteTraceCounit A f L' τ).app K) = 𝟙 _) := by
  let L := CoordinateTrace.shiftedLine A J d
  have he₂ := (CoordinateTrace.contractions A f J hJ d t₀ t₁ t₂ ht₁ ht₂).2
  let G := CoordinateTrace.H A f L
  let H := ordinaryFiniteTwistedPullback A f L'
  let F := ordinaryFinitePushforward A f
  let e : G ≅ H := Functor.isoWhiskerLeft (ordinaryFinitePullback A f)
    (((flipFunctor _ _ _).obj (ordinaryFiniteTensor A X)).mapIso w)
  let ε' := ordinaryFiniteTraceCounit A f L' τ
  let ε : G ⋙ F ⟶ 𝟭 (DerivedCategoryModule A Y) :=
    Functor.whiskerRight e.hom F ≫ ε'
  have hε (K : DerivedCategoryModule A Y) :
      ε.app K = CoordinateTrace.evaluation A f L t₀ K := by
    as_aux_lemma =>
      change F.map (((ordinaryFiniteTensor A X).obj
        ((ordinaryFinitePullback A f).obj K)).map w.hom) ≫ ε'.app K = _
      dsimp only [ε']
      rw [ordinaryFiniteTraceCounit_coefficient]
      simpa only [ht₀, Category.assoc] using
        ordinaryFiniteTraceCounit_coordinate_evaluation A f L
          ((ordinaryFinitePushforward A f).map w.hom ≫ τ) K
  apply Adjunction.transport_unit_triangles F G H e
    (supportedDiagonalUnit A f L δ) ε ε' rfl
  · exact Adjunction.first_triangle_of_evaluation_eq F G
      (supportedDiagonalUnit A f L δ) ε
      (fun K ↦ CoordinateTrace.evaluation A f L t₀ K) hε
      (scalarFirstTriangle A f J hJ d t₀ δ t₁ t₂ ht₁ ht₂ hi₁)
  · as_aux_lemma =>
      intro K
      rw [hε]
      exact supportedDiagonalUnit_second A f L δ t₀ t₂ he₂ hi₂ K
end AlgebraicGeometry.Etale
