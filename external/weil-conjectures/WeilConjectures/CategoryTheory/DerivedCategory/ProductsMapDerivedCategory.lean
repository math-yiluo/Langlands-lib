/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import WeilConjectures.CategoryTheory.DerivedCategory.Products

/-!
# Exact functors preserving products on derived categories

Let `F : C ⥤ D` be an exact functor between abelian categories with K-injective resolutions in
which products of shape `β` exist and are exact. If `F` preserves products of shape `β`, then so
does the induced functor `F.mapDerivedCategory` on the derived categories: products in the derived
category are computed by degreewise products of complexes
(`DerivedCategory.isLimitFanMkQObj`), which `F` preserves.

## Main statements

- `CategoryTheory.Functor.preservesLimitsOfShape_discrete_mapDerivedCategory`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
  [Abelian.HasKInjectiveResolutions D] {β : Type*}
  [HasLimitsOfShape (Discrete β) C] [HasExactLimitsOfShape (Discrete β) C]
  [HasLimitsOfShape (Discrete β) D] [HasExactLimitsOfShape (Discrete β) D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesLimitsOfShape (Discrete β) F]

/-- An exact functor preserving products of shape `β` induces a functor on derived categories
preserving products of shape `β`, provided products of shape `β` are exact in the source and in
the target. -/
lemma preservesLimitsOfShape_discrete_mapDerivedCategory :
    PreservesLimitsOfShape (Discrete β) F.mapDerivedCategory := by
  have (K : β → DerivedCategory C) : PreservesLimit (Discrete.functor K) F.mapDerivedCategory := by
    let L (b : β) := DerivedCategory.Q.objPreimage (K b)
    have : PreservesLimit (Discrete.functor fun b ↦ DerivedCategory.Q.obj (L b))
        F.mapDerivedCategory := by
      refine preservesLimit_of_preserves_limit_cone
        (DerivedCategory.isLimitFanMkQObj (productIsProduct L)) ?_
      refine (isLimitMapConeFanMkEquiv _ _ _).symm ?_
      let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
      have ht : IsLimit (Fan.mk (G.obj (∏ᶜ L)) fun b ↦ G.map (Pi.π L b)) :=
        isLimitFanMkObjOfIsLimit G L _ (productIsProduct L)
      exact Fan.IsLimit.ofIsos (DerivedCategory.isLimitFanMkQObj ht)
        (fun b ↦ F.mapDerivedCategoryFactors.app (L b)) (F.mapDerivedCategoryFactors.app (∏ᶜ L))
        (fun b ↦ (F.mapDerivedCategoryFactors.hom.naturality (Pi.π L b)).symm)
    exact preservesLimit_of_iso_diagram _ (Discrete.natIso fun b ↦
      DerivedCategory.Q.objObjPreimageIso (K b.as) :
        Discrete.functor (fun b ↦ DerivedCategory.Q.obj (L b)) ≅ Discrete.functor K)
  exact preservesLimitsOfShape_of_discrete _

end CategoryTheory.Functor
