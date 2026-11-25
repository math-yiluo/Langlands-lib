/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.DirectImageReductionMapLevelwiseIso
import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.DirectImageReductionMapLevelwiseDetection

/-! # Isomorphism of the direct-image reduction mate

Source: literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/prop-weil-pbc-direct-image-limits.proof.md, proof (2).
(blueprint: lem-weil-pbc-direct-image-completion-compatibility-isIso)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The direct-image reduction mate is invertible at every derived object.

Proof source: proof (2) of the direct-image limits proposition. Represent K by a
K-injective complex I. The finite scalar cone model, strict direct-image cone
comparison, and split-perfect tensor K-injectivity identify each finite evaluation
of the mate with an isomorphism. Apply levelwise detection in complete derived
completion. This is the K-injective/levelwise-detection subclaim isolated from
the parent proposition.
(blueprint: lem-weil-pbc-direct-image-completion-compatibility-isIso) -/
theorem directImage_pushReductionMap_isIso :
    ∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      IsIso ((mateEquiv (moduleAdjunction l E f) (towerAdjunction l E f)
        (.mk _ _ _ _ (pullReduction l E f).hom)).app K) := by
  intro K
  apply directImage_pushReductionMap_levelwiseDetection l E (T := Y)
    ((mateEquiv (moduleAdjunction l E f) (towerAdjunction l E f)
      (.mk _ _ _ _ (pullReduction l E f).hom)).app K)
  intro n
  exact directImage_pushReductionMap_levelwiseIso l E f K n

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
