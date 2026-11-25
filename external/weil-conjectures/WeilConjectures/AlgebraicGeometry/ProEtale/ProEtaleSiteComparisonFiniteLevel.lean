/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-!
# Exactness, the unit, and injective acyclicity of finite-coefficient comparison
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- For a finite discrete ring, comparison inverse image is exact, the canonical unit
is invertible on every etale module sheaf, and pulled-back injectives have zero positive
higher comparison direct images. -/
theorem siteComparison_finiteLevel (T : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ] :
    PreservesFiniteLimits (comparisonUpperStar (ModuleCat.{u + 1} Λ) T) ∧
    PreservesFiniteColimits (comparisonUpperStar (ModuleCat.{u + 1} Λ) T) ∧
    (∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsIso ((T.proEtaleSiteComparisonModules Λ).unit.app F)) ∧
    (∀ (I : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (_ : Injective I)
      (q : ℕ), 0 < q →
      IsZero (((comparisonLowerStar (ModuleCat.{u + 1} Λ) T).rightDerived q).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) T).obj I))) := by
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · intro F
    change IsIso ((comparisonAdjunction (ModuleCat.{u + 1} Λ) T).unit.app F)
    have := isIso_comparisonAdjunction_unit (ModuleCat.{u + 1} Λ) T
    infer_instance
  · intro I hI q hq
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
    exact rightAcyclic_comparisonUpperStar_obj_of_injective (ModuleCat.{u + 1} Λ) T I n

end AlgebraicGeometry.ProEtale
