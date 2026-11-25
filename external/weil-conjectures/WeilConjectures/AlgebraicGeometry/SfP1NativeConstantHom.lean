/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction

/-! # Reassociation of the native constant inverse-image comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u uB
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.SfP1Transport
attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.leftDerivedFunctor
  Functor.mapDerivedCategory DerivedCategory.singleFunctors upperStar

/-- The single-degree constant comparison reassociates to the native constant comparison.
Source: blueprint thm-amb-p1-adjunction.proof.md, constant-object comparisons.
(auxiliary; not a blueprint node).

Proof: the single-degree left-derived comparison consists of the exact-derived
comparison followed by the exact single-degree comparison. Composing with the
single image of the sheaf-level constant comparison supplies the three factors
in the native constant comparison. Associativity changes their parentheses. -/
theorem nativeConstant_hom
    (B : Type uB) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : B) :
    (singleFunctorCompLeftDerivedUpperStarIso B f).hom.app
        ((constantSheaf Y.smallEtaleTopology B).obj M) ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((Scheme.upperStarConstantSheafIso B f).hom.app M) =
    (leftDerivedUpperStarSingleConstantSheafIso B f M).hom := by
  exact Category.assoc _ _ _

end AlgebraicGeometry.Etale.SfP1Transport
