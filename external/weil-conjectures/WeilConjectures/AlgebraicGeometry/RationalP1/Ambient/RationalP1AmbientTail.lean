/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.RationalP1AmbientComposites

/-! # The class-free tail of the specified ambient projective-line unit
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] twist firstProjection secondProjection square
attribute [local irreducible] unitComponent twistProjectionMap condensedAmbientExchange

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The native exchange inverse, through the fixed module-object functor names. -/
@[irreducible]
def ambientExchangeInverse {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (M : DerivedCategory (Modules Λ X))
    (hb : IsIso ((condensedAmbientExchange Λ sq).app M)) :
    (moduleObjectDerivedPushforward Λ f').obj
      ((moduleObjectDerivedPullback Λ g').obj M) ⟶
    (moduleObjectDerivedPullback Λ g).obj
      ((moduleObjectDerivedPushforward Λ f).obj M) := by
  letI := hb
  unfold moduleObjectDerivedPullback moduleObjectDerivedPushforward
  exact inv ((condensedAmbientExchange Λ sq).app M)

variable (Y : Scheme.{u}) (L : ∀ X : Scheme.{u}, Modules Λ X)
  (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
    (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
      (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧) ≅
    ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
      (L (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
  (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
  (hb : IsIso ((condensedAmbientExchange Λ (square Y)).app M))
  (hp : IsIso (twistProjectionMap Λ (secondProjection Y)
    (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e
    ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)))

/-- The two class-free arrows at the end of the fixed ambient unit formula. -/
@[irreducible]
def unitTail :
    (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      ((twist Λ (diagonalSurface Y) (L (diagonalSurface Y))).obj
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)) ⟶
    (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
        ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj M)) :=
  haveI := hp
  inv (twistProjectionMap Λ (secondProjection Y)
    (L (ProjectiveLine Y)) (L (diagonalSurface Y)) e
    ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)) ≫
    (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).map
      (ambientExchangeInverse Λ (square Y) M hb)

/-- Separate the literal unit into its insertion and its class-free tail. -/
theorem unitComponent_factor (d : Diagram Λ Y L) :
    unitComponent Λ Y L d e M hb hp =
      (pushSectionIso Λ Y).hom.app M ≫
        (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
          (diagonalClassMap Λ Y L d M) ≫ unitTail Λ Y L e M hb hp := by
  unfold unitComponent unitTail ambientExchangeInverse
  with_unfolding_all rfl

end AlgebraicGeometry.ProEtale.RationalP1
