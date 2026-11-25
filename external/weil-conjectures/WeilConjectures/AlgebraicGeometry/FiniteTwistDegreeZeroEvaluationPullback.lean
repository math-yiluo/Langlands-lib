/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps
import WeilConjectures.AlgebraicGeometry.FiniteTwistDegreeZeroEvaluationPairing
import WeilConjectures.AlgebraicGeometry.FiniteTwistFlatEvaluationPullback

/-! # Pullback of the finite-twist evaluation before shifting

Source: the degree-zero evaluation step of thm-amb-p1-decomposition.proof.md
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] AlgebraicGeometry.Etale.singleFunctorPullbackMap
universe u uB
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize

private theorem evaluation_congr
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {S U : C} {V W V₁ V₂ : D}
    (q q₀ : S ⟶ U) (r r₀ : V ⟶ W) (u u₀ : F.obj U ⟶ W)
    (a : F.obj S ⟶ V₁) (b : V₁ ⟶ V₂) (c : V₂ ⟶ V)
    (hq : q = q₀) (hr : r = r₀) (hu : u = u₀)
    (h : F.map q₀ ≫ u₀ = a ≫ b ≫ c ≫ r₀) :
    F.map q ≫ u = a ≫ b ≫ c ≫ r := by
  rw [hq, hr, hu]
  exact h

private theorem constant_pullback_map
    (B : Type uB) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (V : B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    singleFunctorPullbackMap (B := B) f ((Scheme.upperStarConstantSheafIso B f).app V).hom =
      (genericConstantIso B V f).hom := by
  delta singleFunctorPullbackMap
  rfl

private theorem positive_flat
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    ObjectProperty.flat (Scheme.finiteEtaleTateLine T N A hA) :=
  ObjectProperty.flat_of_tensorIso (p1DecompositionSheafProduct A N hN hA T hT)

/-- The normalized finite-line evaluation commutes with derived inverse image in degree zero.

Source: Stacks Tags 03PK and 06YQ; the degree-zero step of the evaluation identification
in thm-amb-p1-decomposition.proof.md
(auxiliary; not a blueprint node).

Proof: apply the negative normalization of the canonical twist transport at n=0.
Its zero normalization identifies the output with constant-sheaf pullback. The
positive line is flat by its normalized inverse product. Apply the flat single-object tensor
compatibility theorem to that ordinary evaluation square. Derived pullback preserves
symmetry; naturality moves the two factor comparisons through the symmetry, yielding
the displayed reversed-factor evaluation square. This argument also covers zero
coefficients and empty schemes. -/
theorem finiteTwistDegreeZeroEvaluation_pullback
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (ordinaryFinitePullback A f).map
        (p1DecompositionDegreeZeroEvaluation A N hN hA Y hY) ≫
        (ordinaryFiniteUnitPullback A f).hom =
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A N Y hA (-1)))).app (ordinaryFiniteLine A N hA Y) ≫
      ((ordinaryFiniteTensor A X).obj ((ordinaryFinitePullback A f).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A N Y hA (-1))))).map
        (singleFunctorPullbackMap (B := ModuleCat.{u + 1} A) f
          (L := Scheme.finiteEtaleTateLine Y N A hA)
          (L' := Scheme.finiteEtaleTateLine X N A hA)
          (p1DecompositionSheafPullback A N hN hA f hY 1).hom) ≫
      ((ordinaryFiniteTensor A X).map
        (singleFunctorPullbackMap (B := ModuleCat.{u + 1} A) f
          (p1DecompositionSheafPullback A N hN hA f hY (-1)).hom)).app
          (ordinaryFiniteLine A N hA X) ≫
      p1DecompositionDegreeZeroEvaluation A N hN hA X
        ((map_natCast f.appTop.hom N) ▸ hY.map f.appTop.hom) := by
  let hX := (map_natCast f.appTop.hom N) ▸ hY.map f.appTop.hom
  exact evaluation_congr (ordinaryFinitePullback A f) _ _ _ _ _ _ _ _ _
    (finiteTwistDegreeZeroEvaluation_pairing A N hN hA Y hY
      (positive_flat A N hN hA Y hY))
    (finiteTwistDegreeZeroEvaluation_pairing A N hN hA X hX
      (positive_flat A N hN hA X hX))
    (constant_pullback_map (ModuleCat.{u + 1} A) (ModuleCat.of A A) f).symm
    (finiteTwistFlatEvaluation_pullback A N hN hA f hY
      (positive_flat A N hN hA Y hY) (positive_flat A N hN hA X hX))

end AlgebraicGeometry.Etale
