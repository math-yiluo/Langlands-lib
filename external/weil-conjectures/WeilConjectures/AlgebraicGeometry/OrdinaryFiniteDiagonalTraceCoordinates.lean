/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDiagonalChartExchange
import WeilConjectures.AlgebraicGeometry.FiniteShiftedLineSquare
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalIntegral
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceBaseChange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackNormalization
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# The chart traces satisfy the two self-exchange equations -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 20000] SymmetricCategory.toBraidedCategory
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
  AlgebraicGeometry.ProjectiveSpace

/-- The coefficient line pulled from the original base, normalized on either projection. -/
def ordinaryFiniteDiagonalCoefficientIso
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (S : Scheme.{u})
    (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    (ordinaryFinitePullback A (projectiveLineDiagonalProjection S a)).obj
        ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj
          ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)) ≅
      (ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧ :=
  (ordinaryFinitePullback A (projectiveLineDiagonalProjection S a)).mapIso
      (ordinaryFiniteShiftedLinePullback A N hA t (ProjectiveLine S ↘ S) hS) ≪≫
    ordinaryFiniteShiftedLinePullback A N hA t (projectiveLineDiagonalProjection S a)
      (affineTraceProjectiveInvertible N S hS)

/-- The scalar chart trace satisfies exchange with the original projective-line trace. -/
theorem ordinaryFiniteDiagonalTrace_exchange
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (c : OrdinaryFiniteP1ChernFamily A N hA)
    (b : ∀ (T : Scheme.{u}) [IsNoetherian T] (_hT : IsUnit (N : Γ(T, ⊤))),
      ((ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A T) ≅
        (ordinaryFinitePushforward A (ProjectiveLine T ↘ T)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine T))⟦(2 : ℤ)⟧))
    (hb : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      (b T hT).hom = ordinaryFiniteP1KummerMap A N hA t c T hT)
    (hbc : OrdinaryFiniteP1KummerMapBaseChange A N hA t c)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    let : IsLocallyNoetherian (ProjectiveLine S) :=
      LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
    let : CompactSpace (ProjectiveLine S) :=
      QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
    let : IsNoetherian (ProjectiveLine S) := ⟨⟩
    ∀ a : Bool,
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) (projectiveLineDiagonalSquare S a)).app
          ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).obj
            ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)) ≫
        (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
          (ordinaryFiniteDiagonalCoefficientIso A N hA t S hS (!a)).hom ≫
        ordinaryFiniteP1DiagonalChartMap A N hA t S hS a ≫
        (b (ProjectiveLine S) (affineTraceProjectiveInvertible N S hS)).inv ≫ biprod.snd ≫
        (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) (ProjectiveLine S)).hom =
      (ordinaryFinitePullback A (ProjectiveLine S ↘ S)).map
        ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map
            (ordinaryFiniteShiftedLinePullback A N hA t (ProjectiveLine S ↘ S) hS).hom ≫
          (b S hS).inv ≫ biprod.snd ≫
          (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S).hom) ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) (ProjectiveLine S ↘ S)).hom := by
  let : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
  let : CompactSpace (ProjectiveLine S) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
  let : IsNoetherian (ProjectiveLine S) := ⟨⟩
  dsimp only
  intro a
  let q := ProjectiveLine S ↘ S
  let hP := affineTraceProjectiveInvertible N S hS
  have ht := ordinaryFiniteP1_scalarTrace_baseChange N A hA t c b hb hbc q hS hP
  rw [ordinaryFiniteP1Exchange_eq_derived] at ht
  have hn := (derivedBaseChangeMap (ModuleCat.{u + 1} A)
    (projectiveLineDiagonalSquare S a)).naturality
      (ordinaryFiniteShiftedLinePullback A N hA t q hS).hom
  dsimp only [Functor.comp_map] at hn
  simp only [ordinaryFiniteDiagonalCoefficientIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  erw [← Category.assoc, ← hn, Category.assoc]
  rw [reassoc_of% ordinaryFiniteDiagonalChart_exchange A N hN hA t S hS a]
  erw [← reassoc_of% ht]
  simp only [Functor.map_comp, Category.assoc]
  erw [ordinaryFiniteUnitPullback_hom_unit]
  erw [Functor.map_comp (ordinaryFinitePullback A q)
    (biprod.snd : ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞
      ordinaryFiniteUnit A S) ⟶ ordinaryFiniteUnit A S)
    (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) S).hom]
  erw [Category.assoc]
  rfl

/-- The two coefficient identifications agree with the common-base coordinate comparison. -/
theorem ordinaryFiniteDiagonalCoefficientIso_coordinate
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    (CoordinateTrace.coordinate A (ProjectiveLine S ↘ S)
        ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧)).hom ≫
      (ordinaryFiniteDiagonalCoefficientIso A N hA t S hS true).hom =
        (ordinaryFiniteDiagonalCoefficientIso A N hA t S hS false).hom := by
  have _ := hN
  exact ordinaryFiniteShiftedLinePullback_square A N hA t
    (CommSq.mk (pullback.condition (f := ProjectiveLine S ↘ S)
      (g := ProjectiveLine S ↘ S)).symm) hS
    (affineTraceProjectiveInvertible N S hS) (affineTraceProjectiveInvertible N S hS)

end AlgebraicGeometry.Etale
