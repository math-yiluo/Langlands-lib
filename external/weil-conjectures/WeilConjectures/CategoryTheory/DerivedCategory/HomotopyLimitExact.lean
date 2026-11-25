/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ProductsMapDerivedCategory
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit

/-!
# Exact functors preserve derived limits of towers

`CategoryTheory.Functor.isHomotopyLimit_mapDerivedCategory_mapCone`: an exact functor between
abelian categories with exact countable products, which preserves countable products, sends
homotopy limit cones in the derived category to homotopy limit cones: `F.mapDerivedCategory` is
triangulated and preserves countable products
(`CategoryTheory.Functor.preservesLimitsOfShape_discrete_mapDerivedCategory`).
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
  [Abelian.HasKInjectiveResolutions D]
  [HasLimitsOfShape (Discrete ℕ) C] [HasExactLimitsOfShape (Discrete ℕ) C]
  [HasLimitsOfShape (Discrete ℕ) D] [HasExactLimitsOfShape (Discrete ℕ) D]
  (Φ : C ⥤ D) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  [PreservesLimitsOfShape (Discrete ℕ) Φ]

/-- **Exact functors preserving countable products preserve derived limits of towers**: the
induced functor on derived categories is triangulated and preserves countable products, so it
sends Milnor triangles to Milnor triangles. -/
lemma isHomotopyLimit_mapDerivedCategory_mapCone {F : ℕᵒᵖ ⥤ DerivedCategory C}
    {c : Cone F} (hc : IsHomotopyLimit c) :
    IsHomotopyLimit (Φ.mapDerivedCategory.mapCone c) :=
  have := Φ.preservesLimitsOfShape_discrete_mapDerivedCategory (β := ℕ)
  hc.map Φ.mapDerivedCategory

end CategoryTheory.Functor
