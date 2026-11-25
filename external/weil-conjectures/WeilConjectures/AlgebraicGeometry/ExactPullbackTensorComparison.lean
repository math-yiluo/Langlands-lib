/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-! # Canonical exact pullback tensor comparison

Source: Stacks Tag 0F1E (auxiliary; not a blueprint node).
The foundational comparisons are separated from support localization to avoid a dependency
through smooth duality. Their definitions and public signatures are unchanged.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Etale

variable (E : Type v) [Category.{u + 1} E] [Abelian E]
  [IsGrothendieckAbelian.{u + 1} E] [MonoidalCategory E] [MonoidalPreadditive E]
  [SymmetricCategory E] [MonoidalClosed E] [Abelian.HasFunctorialFlatResolution E]
  [UpperStarPreservesFlat E]

/-- Tensor an isomorphism in each variable using the recorded derived tensor bifunctor.
Source: Tag 0F1E (auxiliary; not a blueprint node). -/
noncomputable def supportDerivedTensorIso
    (T : Scheme.{u}) {K K' L L' : DerivedCategory (Sheaf T.smallEtaleTopology E)}
    (e : K ≅ K') (d : L ≅ L') :
    ((derivedTensor E T).obj K).obj L ≅
      ((derivedTensor E T).obj K').obj L' :=
  ((derivedTensor E T).mapIso e).app L ≪≫
    ((derivedTensor E T).obj K').mapIso d

/-- The exact inverse image tensor comparison uses the canonical K-flat comparison.
Source: Tag 0F1E (auxiliary; not a blueprint node). -/
noncomputable def supportExactPullbackTensorIso
    {S T : Scheme.{u}} (h : S ⟶ T) (K L : DerivedCategory (Sheaf T.smallEtaleTopology E)) :
    (upperStar E h).mapDerivedCategory.obj
        (((derivedTensor E T).obj K).obj L) ≅
      ((derivedTensor E S).obj
        ((upperStar E h).mapDerivedCategory.obj K)).obj ((upperStar E h).mapDerivedCategory.obj L)
      :=
  (leftDerivedUpperStarIsoMapDerivedCategory E h).symm.app
      (((derivedTensor E T).obj K).obj L) ≪≫
    leftDerivedUpperStarTensorIso E h K L ≪≫
    supportDerivedTensorIso E S
      ((leftDerivedUpperStarIsoMapDerivedCategory E h).app K)
      ((leftDerivedUpperStarIsoMapDerivedCategory E h).app L)

end AlgebraicGeometry.Etale
