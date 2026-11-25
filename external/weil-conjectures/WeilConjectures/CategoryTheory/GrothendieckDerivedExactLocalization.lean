/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful

@[expose] public section
universe w uA vA vH
open CategoryTheory.Limits
namespace CategoryTheory

/-- Exact derived Gabriel--Popescu localization for an exact module-category presentation.

Source: Stacks Project, Tags 0F5V and 0F5X.
(auxiliary; not a blueprint node)

The abelian Gabriel--Popescu adjunction is fixed as the source of the construction. Its
invertible counit makes the right adjoint fully faithful; exactness of the left adjoint
allows the right adjoint to preserve K-injective complexes, so the source adjunction
lifts to the unbounded derived categories.
-/
theorem grothendieckDerived_exact_localization
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    {S : Type w} [Ring S] [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)]
    (F : ModuleCat.{max w vH} S ⥤ A) (U : A ⥤ ModuleCat.{max w vH} S)
    (adj₀ : F ⊣ U) [F.Additive] [U.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hc₀ : IsIso adj₀.counit) :
    F.mapDerivedCategory.IsTriangulated ∧
      IsIso adj₀.mapDerivedCategoryRightDerivedAdjunction.counit := by
  let : IsIso adj₀.counit := hc₀
  let hff : U.FullyFaithful := adj₀.fullyFaithfulROfIsIsoCounit
  let : U.Full := hff.full
  let : U.Faithful := hff.faithful
  let : U.PreservesKInjectiveComplexes := adj₀.preservesKInjectiveComplexes
  constructor
  · infer_instance
  · infer_instance

end CategoryTheory
