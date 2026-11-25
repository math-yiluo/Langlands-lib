/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletion

/-! # Levelwise detection of isomorphisms of derived reduction towers

Source: literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/prop-weil-pbc-direct-image-limits.proof.md, proof (2), via
proposition-proper-base-change-complete-integral.
(blueprint: lem-weil-pbc-direct-image-completion-compatibility-levelwise-detection)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject
  AdicCompletion.ringCommutative AdicCompletion.modulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {T : Scheme.{u}}

/-- Isomorphisms of derived reduction towers are detected at every finite level.
Source: proposition-proper-base-change-complete-integral, conservativity of the derived evaluations.
Proof: apply the reverse implication of the evaluation-conservativity clause of
`completeDerivedCompletion` to the identity morphism of the base scheme.
(blueprint: lem-weil-pbc-direct-image-completion-compatibility-levelwise-detection) -/
theorem directImage_pushReductionMap_levelwiseDetection
    {M N : CompleteDerivedCompletion.DTow l E T} (a : M ⟶ N)
    (ha : ∀ n : ℕ, IsIso ((CompleteDerivedCompletion.dev l E T n).map a)) :
    IsIso a := by
  exact ((completeDerivedCompletion l E T T (𝟙 T)).2.2.1 a).mpr ha

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
