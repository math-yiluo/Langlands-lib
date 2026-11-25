/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimensionSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Topology.KrullDimension

/-! # The direct-image finiteness input

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/
`theorem-results-from-etale-theory` (blueprint: theorem-results-from-etale-theory).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The two ordinary direct-image finiteness conditions used in the exceptional-image
construction, with a signed integer annihilator `N`. The first clause requires every
nonnegative higher direct image of a constructible module sheaf along a finite-type
morphism of finite-type `k`-schemes to be constructible. The second clause quantifies
over separably closed fields `K` with `N` invertible and finite-type `K`-schemes of
dimension at most `d`, requiring vanishing above `2 * d` for every locally torsion
abelian sheaf; it does not require a uniform annihilator for that sheaf.
Source: blueprint `sec-smooth-purity/sk-prop-a1-kummer/def-exc-direct-image-input.md`
(blueprint: theorem-results-from-etale-theory). -/
def HasDirectImageFinitenessInput
    (k : Type u) [Field k] (N : ℤ) (_hN : IsUnit (N : k))
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (_hΛ : ∀ a : Λ, N • a = 0) : Prop :=
  (∀ {S T : Scheme.{u}}
      (aS : S ⟶ Spec (.of k)) (aT : T ⟶ Spec (.of k))
      [LocallyOfFiniteType aS] [QuasiCompact aS]
      [LocallyOfFiniteType aT] [QuasiCompact aT]
      (uST : S ⟶ T) [LocallyOfFiniteType uST] [QuasiCompact uST]
      (_hu : uST ≫ aT = aS)
      (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (_hF : IsConstructibleEtaleModuleSheaf F) (q : ℕ),
      IsConstructibleEtaleModuleSheaf
        ((DerivedCategory.homologyFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)).obj
          ((Etale.rightDerivedLowerStar (ModuleCat.{u + 1} Λ) uST).obj
            ((DerivedCategory.singleFunctor
                (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F)))) ∧
    (∀ (d : ℕ) (K : Type u) [Field K] [IsSepClosed K]
      (_hK : IsUnit (N : K)) (W : Scheme.{u})
      (aW : W ⟶ Spec (.of K)) [LocallyOfFiniteType aW] [QuasiCompact aW]
      (_hd : topologicalKrullDim W ≤ (d : WithBot ℕ∞)),
      HasTorsionEtaleCohomologicalDimensionLE W (2 * d))

end AlgebraicGeometry.Scheme

