/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompleteDerivedCompletion
public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.DirectImageRoosLimitData

/-! Canonical derived-limit projection normalization. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
/-- The conjugate limit comparison preserves the canonical counit projections.
Source: blueprint direct-image limits, proof (1); Stacks Tag 0A07.
(blueprint: lem-pbc-direct-image-roos-projection-compatibility)

Proof: expand pushLimitIso as the conjugate of constantInterchange under the two
composite adjunctions. The counit identity for conjugate transformations expresses
constant of this comparison followed by the target counit as pushforward of the
source counit, after the constant/pullback interchange. Evaluate this identity at n.
The evaluation mate identity moves pushEvaluationMap through the tower counit.
Coherence of exact localization identifies constantInterchange followed by
pullEvaluation with the two canonical constantEvaluationIso components. Cancel
these components and use their naturality. The remaining equality is precisely
the displayed square, naturally in M; the adjunction triangle identities give
the same formula for identity morphisms and zero towers. -/
theorem directImage_roos_projection_compatibility {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DTow l E X) (n : ℕ) :
    (pushLimitIso l E f).hom.app M ≫
        (levelProjection l E Y n).app ((rpush l E f).obj M) ≫
        (pushEvaluationMap l E f n).app M =
      (rpushModule l E f).map ((levelProjection l E X n).app M) := by
  sorry

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
