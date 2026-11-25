/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1ChartExchange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp
import WeilConjectures.AlgebraicGeometry.SfP1ConstantUnitPullback
import WeilConjectures.AlgebraicGeometry.SfP1PresentationExchange
import WeilConjectures.AlgebraicGeometry.SfP1TraceTransportPasting

/-! # True projection case of projective-line trace transport

This is the fixed-`true` component of the arbitrary-trace transport equation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local instance 1000000] instCategoryDerivedCategory

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace

attribute [local implicit_reducible] ordinaryFiniteDegreeZero ordinaryFiniteSingleFunctor
attribute [local irreducible] upperStar lowerStar DerivedCategory.singleFunctors

private theorem unit_transport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i.hom
        (ProjectiveLine S ↘ S) f hi.symm).hom.app (ordinaryFiniteUnit A S) ≫
      (ordinaryFinitePullback A i.hom).map
        (ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom ≫
      (constantComparison A i).hom =
    (ordinaryFinitePullback A f).map (constantUnit A S).hom ≫
      (leftDerivedUpperStarDerivedTensorUnitIso f).hom := by
  unfold constantComparison
  rw [Iso.trans_hom, reassoc_of% (ordinaryFiniteUnitPullback_comp A i.hom
    (ProjectiveLine S ↘ S) f hi.symm)]
  exact constantUnit_pullback A f

/-- Paste the geometric family before choosing the coefficient objects. -/
private theorem pastingWithFamily
    {C D E W Z : Type*} [Category C] [Category D] [Category E]
    [Category W] [Category Z]
    (P : C ⥤ D) (Q : E ⥤ C) (F : E ⥤ D) (H : C ⥤ E)
    (R : Z ⥤ D) (R₀ : W ⥤ C) (U : W ⥤ Z) (V : C ⥤ W)
    (W₀ : D ⥤ Z) (T : D ⥤ E) (T₀ : D ⥤ E) (z : T ≅ T₀)
    (b : U ⋙ R ≅ R₀ ⋙ P) (d : H ⋙ Q ≅ V ⋙ R₀)
    (s : P ⋙ W₀ ≅ V ⋙ U) (e : T ⋙ F ≅ W₀ ⋙ R) (c : F ≅ Q ⋙ P)
    (g : ∀ B : C, T₀.obj (P.obj B) ⟶ H.obj B)
    (hb : ∀ B : C, b.hom.app (V.obj B) ≫ P.map (d.inv.app B) =
      R.map (s.inv.app B) ≫ e.inv.app (P.obj B) ≫
        F.map (z.hom.app (P.obj B) ≫ g B) ≫ c.hom.app (H.obj B))
    {B : C} {B' : D} {L : W} {K : Z}
    (a : U.obj L ≅ K) (v : V.obj B ≅ L) (l : P.obj B ≅ B')
    (k : W₀.obj B' ≅ K)
    {J J' : E} {J₀ : C} {J₁ : D}
    (u : J ⟶ J') (uQ : Q.obj J ⟶ J₀) (uP : P.obj J₀ ⟶ J₁)
    (uF : F.obj J' ⟶ J₁) (τ : H.obj B ⟶ J)
    (ha : a.inv ≫ U.map v.inv ≫ s.inv.app B = k.inv ≫ W₀.map l.inv)
    (hu : c.hom.app J ≫ P.map uQ ≫ uP = F.map u ≫ uF) :
    middleComposite R b a ≫ P.map (R₀.map v.inv ≫ d.inv.app B) ≫
        P.map (Q.map τ ≫ uQ) ≫ uP =
      R.map k.inv ≫ e.inv.app B' ≫
        F.map (traceComposite T T₀ z l (g B) τ u) ≫ uF := by
  exact traceTransportPasting P Q F H R R₀ U V W₀ T b d s e c
    a v l k T₀ z (g B) u uQ uP uF τ (hb B) ha hu

set_option linter.defProp false in
/-- Fix the geometry before substituting any coefficient objects. -/
@[irreducible] private def categoricalPasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f) :=
  @pastingWithFamily
    (DerivedCategoryModule A (ProjectiveLine S)) (DerivedCategoryModule A X)
    (DerivedCategoryModule A S)
    (DerivedCategoryModule A
      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))
    (DerivedCategoryModule A (pullback f f))
    _ _ _ _ _
    (ordinaryFinitePullback A i.hom)
    (ordinaryFinitePullback A (ProjectiveLine S ↘ S))
    (ordinaryFinitePullback A f)
    (ordinaryFinitePushforward A (ProjectiveLine S ↘ S))
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f f))
    (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S true))
    (ordinaryFinitePullback A (productMap f i hi))
    (ordinaryFinitePullback A (projectiveLineDiagonalProjection S false))
    (ordinaryFinitePullback A (pullback.fst f f))
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (ordinaryFinitePushforward A f)
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) f)
    (secondProjectionComparison A f i hi)
    (properExchange A (projectiveProjectionSquare S true))
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A)
      (firstProjectionSquare f i hi).toCommSq)
    (TraceDiagonalDatum.baseChangeIso (Λ := A) f)
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i.hom
      (ProjectiveLine S ↘ S) f hi.symm)
    (presentationTrace A f i hi) (presentationExchange A f i hi)

set_option linter.defProp false in
@[irreducible] private def linePasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (N : Γ(S, ⊤))) :=
  @categoricalPasting A inferInstance inferInstance S X f inferInstance i hi
    ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)
    ((ordinaryFiniteLine A N hA
      (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧)
    ((CoordinateTrace.pull A (pullback.snd f f)).obj
      ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧))
    (coefficientComparison A N hA t f i hi hS)
    (ordinaryFiniteShiftedLinePullback A N hA t
      (projectiveLineDiagonalProjection S false)
      (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS))
    (ordinaryFiniteShiftedLinePullback A N hA t i.hom
      (finiteP1_unitOnPullback N (ProjectiveLine S ↘ S) hS))
    (SfDiagonalKernel.coordinate A f
      (CoordinateTrace.shiftedLine A (Scheme.finiteEtaleTateLine S N A hA) 1)
      (ordinaryFiniteShiftedLinePullback A N hA t f hS).symm)
private theorem middleComposite_change_functor
    {C D E T : Type*} [Category C] [Category D] [Category E] [Category T]
    {U : C ⥤ D} {H : C ⥤ E} {P : E ⥤ T}
    (R R' : D ⥤ T) (e : R ≅ R') (b : U ⋙ R ≅ H ⋙ P)
    {L : C} {K : D} (a : U.obj L ≅ K) :
    middleComposite (F := U) (H := H) (P := P) R b a = e.hom.app K ≫
      middleComposite (F := U) (H := H) (P := P) R'
        (Functor.isoWhiskerLeft U e.symm ≪≫ b) a := by
  unfold middleComposite
  change R.map a.inv ≫ b.hom.app L =
    e.hom.app K ≫ R'.map a.inv ≫ e.inv.app (U.obj L) ≫ b.hom.app L
  rw [← reassoc_of% (e.hom.naturality a.inv), Iso.hom_inv_id_app_assoc]

section ProjectionNormalization

attribute [local semireducible] projection
attribute [local implicit_reducible] projection

private theorem middleComparison_true_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (N : Γ(S, ⊤))) :
    middleComparison A N hA t f i hi hS true =
      (eqToIso (secondProjectionShriek_eq A f)).hom.app
          ((CoordinateTrace.pull A (pullback.snd f f)).obj
            ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)) ≫
        middleComposite
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f f))
          (secondProjectionComparison A f i hi) (coefficientComparison A N hA t f i hi hS) := by
  unfold middleComparison secondProjectionComparison
  exact middleComposite_change_functor _ _ (eqToIso (secondProjectionShriek_eq A f))
    (projectionComparison A f i hi true) (coefficientComparison A N hA t f i hi hS)

private theorem pull_map_eq_recorded (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : DerivedCategoryModule A Y} (g : K ⟶ L) :
    (CoordinateTrace.pull A f).map g = (ordinaryFinitePullback A f).map g := by
  unfold CoordinateTrace.pull ordinaryFinitePullback
  rfl

private theorem coordinateTrace_true_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (N : Γ(S, ⊤)))
    (τ : ordinaryFiniteP1SplittingTarget A N hA S ⟶ ordinaryFiniteUnit A S) :
    coordinateTrace A N hA t f i hi hS τ true =
      (eqToIso (secondProjectionShriek_eq A f)).hom.app
          ((CoordinateTrace.pull A (pullback.snd f f)).obj
            ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f f)).map
          (SfDiagonalKernel.coordinate A f
            (CoordinateTrace.shiftedLine A (Scheme.finiteEtaleTateLine S N A hA) 1)
            (ordinaryFiniteShiftedLinePullback A N hA t f hS).symm).inv ≫
        (TraceDiagonalDatum.baseChangeIso (Λ := A) f).inv.app
          ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePullback A f).map (trace A N hA t f i hi hS τ) ≫
        (leftDerivedUpperStarDerivedTensorUnitIso f).hom := by
  rw [secondProjectionShriek_hom_app]
  erw [Category.id_comp]
  unfold coordinateTrace
  dsimp only [Bool.casesOn]
  (rw [pull_map_eq_recorded A f]; rfl)

end ProjectionNormalization

set_option linter.defProp false in
@[irreducible] private def rawPastingResult
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (N : Γ(S, ⊤)))
    (τ : ordinaryFiniteP1SplittingTarget A N hA S ⟶ ordinaryFiniteUnit A S) :=
  linePasting A N hA t f i hi hS
    (J := ordinaryFiniteUnit A S)
    (J' := derivedTensorUnit (ModuleCat.{u + 1} A) S)
    (J₀ := ordinaryFiniteUnit A (ProjectiveLine S))
    (J₁ := derivedTensorUnit (ModuleCat.{u + 1} A) X)
    (constantUnit A S).hom
    (ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom
    (constantComparison A i).hom (leftDerivedUpperStarDerivedTensorUnitIso f).hom τ
    (coordinateLineComparison A N hA t f i hi hS)
    (unit_transport A f i hi)

private theorem nativeProjectionTransport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (N : Γ(S, ⊤)))
    (τ : ordinaryFiniteP1SplittingTarget A N hA S ⟶ ordinaryFiniteUnit A S) :
    middleComposite
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f f))
        (secondProjectionComparison A f i hi) (coefficientComparison A N hA t f i hi hS) ≫
      (ordinaryFinitePullback A i.hom).map (projectionExchange A N hA t S hS true) ≫
      (ordinaryFinitePullback A i.hom).map
        ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).map τ ≫
          (ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom) ≫
      (constantComparison A i).hom =
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f f)).map
        (SfDiagonalKernel.coordinate A f
          (CoordinateTrace.shiftedLine A (Scheme.finiteEtaleTateLine S N A hA) 1)
          (ordinaryFiniteShiftedLinePullback A N hA t f hS).symm).inv ≫
      (TraceDiagonalDatum.baseChangeIso (Λ := A) f).inv.app
        ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePullback A f).map (trace A N hA t f i hi hS τ) ≫
      (leftDerivedUpperStarDerivedTensorUnitIso f).hom := by
  unfold projectionExchange trace
  exact rawPastingResult A N hA t f i hi hS τ

private theorem transport_change_source
    {C : Type*} [Category C] {U V W T : C}
    (e : U ≅ V) {m : U ⟶ W} {n : V ⟶ W} {p : W ⟶ T}
    {c : U ⟶ T} {d : V ⟶ T}
    (hm : m = e.hom ≫ n) (hc : c = e.hom ≫ d) (h : n ≫ p = d) :
    m ≫ p = c := by
  rw [hm, hc, Category.assoc, h]

/--
The ordinary inverse-exchange trace transport for the second projection.

This is the `a = true` component of
`lem-sf-p1-projection-trace-transport`.  The pasted second product square has
both composites to the base equal, which supplies the inverse coordinate factor
in `coordinateTrace`; the twist comparisons are determined by their roots and
pure-scalar generators.  Naturality carries the arbitrary arrow `τ` through the
remaining exchange factors, and the constant sheaf unit comparison is preserved
by inverse image.  The argument is valid for empty bases and zero coefficient
rings.
(auxiliary; not a blueprint node)
-/
theorem projectionTraceTransport_true
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (hS : IsUnit (N : Γ(S, ⊤)))
    (τ : ordinaryFiniteP1SplittingTarget A N hA S ⟶ ordinaryFiniteUnit A S) :
    middleComparison A N hA t f i hi hS true ≫
        (ordinaryFinitePullback A i.hom).map (projectionExchange A N hA t S hS true) ≫
        (ordinaryFinitePullback A i.hom).map
          ((ordinaryFinitePullback A (ProjectiveLine S ↘ S)).map τ ≫
            (ordinaryFiniteUnitPullback A (ProjectiveLine S ↘ S)).hom) ≫
        (constantComparison A i).hom =
      coordinateTrace A N hA t f i hi hS τ true := by
  exact transport_change_source
    ((eqToIso (secondProjectionShriek_eq A f)).app
      ((CoordinateTrace.pull A (pullback.snd f f)).obj
        ((ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)))
    (middleComparison_true_eq A N hA t f i hi hS)
    (coordinateTrace_true_eq A N hA t f i hi hS τ)
    (nativeProjectionTransport A N hA t f i hi hS τ)

end AlgebraicGeometry.Etale.SfP1Transport
