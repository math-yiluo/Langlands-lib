/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.HypercoverCohomologyColimit
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Blueprint statements

corollary-cohomology-pro-etale-affine.
-/

@[expose] public section

universe u₁

open CategoryTheory

namespace AlgebraicGeometry

/-- Blueprint: corollary-cohomology-pro-etale-affine. -/
theorem hypercover_cohomology (X : Scheme.{u₁}) [CompactSpace X] [QuasiSeparatedSpace X]
    (q : ℕ) :
    FiniteSplitEtaleHypercover.IsCohomologyColimit AddCommGrpCat.{u₁ + 1} q
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u₁ + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u₁ + 1} X (q : ℤ)) ∧
    ∀ (R : Type (u₁ + 1)) [Ring R],
      FiniteSplitEtaleHypercover.IsCohomologyColimit (ModuleCat.{u₁ + 1} R) q
        (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u₁ + 1} R)) 0 ⋙
          Etale.cohomology (ModuleCat.{u₁ + 1} R) X (q : ℤ)) := by
  sorry

end AlgebraicGeometry
