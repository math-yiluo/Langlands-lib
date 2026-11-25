/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness

/-! # The shifted finite-twist factor comparisons

Source: Stacks Tags 03PK and 06YQ; the comparison of the two evaluation factors in
thm-amb-p1-decomposition.proof.md
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u uB
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local irreducible] singleFunctorPullbackMap
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize

private noncomputable def positive_transport
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) :
    OrdinaryFiniteTwistTransport A N hA where
  roots := (p1DecompositionTwistTransport A N hN hA).roots
  line := fun f hY ↦ (p1DecompositionTwistTransport A N hN hA).line f hY
    ((map_natCast f.appTop.hom N) ▸ hY.map f.appTop.hom) 1
  roots_normalization := (p1DecompositionTwistTransport A N hN hA).roots_normalization
  line_normalization := fun f hY ↦
    (p1DecompositionTwistTransport A N hN hA).line_normalization f hY _

private theorem positive_line_eq
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    t.line f hY = p1DecompositionSheafPullback A N hN hA f hY 1 := by
  exact congrArg (fun s ↦ s.line f hY)
    (ordinaryFiniteTwistTransport_unique A N hA t (positive_transport A N hN hA))

private theorem shifted_positive_eq
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    ordinaryFiniteShiftedLinePullback A N hA t f hY =
      p1DecompositionTwistPullback A N hN hA f hY 1 2 := by
  unfold ordinaryFiniteShiftedLinePullback
  rw [positive_line_eq A N hN hA t f hY]
  unfold p1DecompositionTwistPullback
  rw [p1DecompositionShiftedComparison]
  rfl

private theorem iso_hom_eq
    {C : Type*} [Category* C] {X Y : C} (e e' : X ≅ Y) (p : X ⟶ Y)
    (h : e = e') (h' : e'.hom = p) : e.hom = p := by
  rw [h]
  exact h'

private theorem generic_shifted_pullback_hom
    (B : Type uB) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Sheaf Y.smallEtaleTopology B) (M : Sheaf X.smallEtaleTopology B)
    (e : (upperStar B f).obj L ≅ M) (b : ℤ) :
    (p1DecompositionShiftedComparison (upperStar B f).leftDerivedFunctor
      (DerivedCategory.singleFunctor _ 0) (DerivedCategory.singleFunctor _ 0)
      (upperStar B f) (singleFunctorCompLeftDerivedUpperStarIso B f) L M e b).hom =
      ((upperStar B f).leftDerivedFunctor.commShiftIso b).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj L) ≫
      (singleFunctorPullbackMap (B := B) f e.hom)⟦b⟧' := by
  rw [p1DecompositionShiftedComparison]
  delta singleFunctorPullbackMap
  rfl

/-- The canonical shifted factor arrows are the shift comparisons of their degree-zero maps.

Source: Stacks Tags 03PK and 06YQ; the factor-comparison step of finite-twist evaluation
(auxiliary; not a blueprint node).

Proof: restrict the canonical signed transport to its positive line and roots.
Its root and line normalizations make it a normalized positive transport, so transport
uniqueness identifies it with the supplied t. This proves the positive shifted
comparison is canonical. Unfold the common shifted-comparison construction for each
factor: its hom is commutation with shift followed by the shifted degree-zero
single-object pullback map. The argument makes no choices and applies to zero
coefficients and empty schemes. -/
theorem finiteTwistShiftedFactorComparisons
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    ((ordinaryFiniteShiftedLinePullback A N hA t f hY).hom =
      (((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor).commShiftIso (2 : ℤ)).hom.app
        (ordinaryFiniteLine A N hA Y) ≫
        (singleFunctorPullbackMap (B := ModuleCat.{u + 1} A) f
          (L := Scheme.finiteEtaleTateLine Y N A hA)
          (L' := Scheme.finiteEtaleTateLine X N A hA)
          (p1DecompositionSheafPullback A N hN hA f hY 1).hom)⟦(2 : ℤ)⟧') ∧
    ((p1DecompositionTwistPullback A N hN hA f hY (-1) (-2)).hom =
      (((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor).commShiftIso (-2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A N Y hA (-1))) ≫
        (singleFunctorPullbackMap (B := ModuleCat.{u + 1} A) f
          (p1DecompositionSheafPullback A N hN hA f hY (-1)).hom)⟦(-2 : ℤ)⟧') := by
  constructor
  · refine iso_hom_eq _ _ _ (shifted_positive_eq A N hN hA t f hY) ?_
    exact generic_shifted_pullback_hom (ModuleCat.{u + 1} A) f
      (Scheme.finiteEtaleTateLine Y N A hA) (Scheme.finiteEtaleTateLine X N A hA)
      (by exact p1DecompositionSheafPullback A N hN hA f hY 1) 2
  · exact generic_shifted_pullback_hom (ModuleCat.{u + 1} A) f
      (Scheme.finiteEtaleTateSheaf A N Y hA (-1))
      (Scheme.finiteEtaleTateSheaf A N X hA (-1))
      (p1DecompositionSheafPullback A N hN hA f hY (-1)) (-2)

end AlgebraicGeometry.Etale
