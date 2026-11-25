/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.DirectImageRoosLimitData
public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.DirectImageCompletionCompatibility

/-!
# Derived direct image, reduction towers and completion

Source: literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/prop-weil-pbc-direct-image-limits.md
(blueprint: proposition-proper-base-change-complete-integral--1).

The reduction projection is the adjunction mate of the normalized cone pullback
comparison. This specifies its finite-level projection-formula normalization, including
the transition maps and the degree-zero inclusions. The limit comparison is the existing
canonical conjugate of the constant/pullback comparison. Its Milnor-cone description in
assertion (1) is stated with the canonical level projections of the derived limit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local instance] Limits.comp_preservesFiniteLimits
  Limits.comp_preservesFiniteColimits

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The reduction/direct-image mate is invertible.
Source: assertion (2) of proposition-proper-base-change-complete-integral--1.
(blueprint: proposition-proper-base-change-complete-integral--1) -/
@[instance] theorem pushReductionMap_isIso : IsIso (pushReductionMap l E f) := by
  have : ∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      IsIso ((pushReductionMap l E f).app K) :=
    fun K ↦ (directImage_completion_compatibility l E f).1 K
  exact NatIso.isIso_of_isIso_app _

/-- The three direct-image assertions, using the actual integral module derived categories.
The canonical arrow in (1) is pushLimitIso, constructed by the constant/pullback
conjugacy, and the evaluation arrow is pushEvaluationMap. Its Milnor-cone description:
the canonical level projections are the first maps of Roos triangles on both sides, the
product comparison of Rf* is invertible and commutes with 1-T, and pushLimitIso is
compatible with the level projections through pushEvaluationMap. The projection in (2) is
pushReductionMap, the mate of the summand-normalized cone comparison; it is a single
natural transformation on derived towers. The displayed equality is exactly (3), before
inverting the projection comparison on its right-hand side.
Source: assertions (1)--(3) (blueprint: proposition-proper-base-change-complete-integral--1).
Proof: (1) is the derived constant-limit adjunction comparison from
completeDerivedCompletion. Its conjugate construction is compatible with the counits,
hence with the level projections after pushEvaluationMap. The Roos comparison of
completeDerivedCompletion gives the triangles with these projections. On the Milnor cone
the map is induced by the product comparison: the right adjoint preserves products, and
projectionwise naturality commutes with 1-T.
For (2) use the preceding K-injective cone computation; the finite-free chain projection
is natural in the resolution, hence respects both the (π,1) transitions and quotient
units. For (3), the square of constant-tower augmentation and projection commutes on
complexes. Apply Rlim and its canonical pushforward comparison. Constant-tower
normalization identifies its initial arrow with Rf*κ. This gives the displayed equality.
If K is complete, κ is invertible; the two comparison isomorphisms then make κ of Rf*K
invertible. The completeness criterion and the same composite give reconstruction.
In Lean, (1) with its Milnor-cone description is `directImage_roos_limit_data`, and
(2)--(3) are `directImage_completion_compatibility`; the proof assembles the two. -/
theorem directImage_limits :
    (∀ n : ℕ, IsIso (pushEvaluationMap l E f n)) ∧
    (∃ (_ : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E X)))
      (_ : HasCountableProducts (DerivedCategory (AdicCompletion.Modules l E Y))),
      ∀ M : DTow l E X,
        (∃ δ, IsDerivedLimitTriangle (fun n : ℕ ↦ (transition l E X n).app M) _
          (Pi.lift fun n : ℕ ↦ (levelProjection l E X n).app M) δ) ∧
        (∃ δ, IsDerivedLimitTriangle
          (fun n : ℕ ↦ (transition l E Y n).app ((rpush l E f).obj M)) _
          (Pi.lift fun n : ℕ ↦ (levelProjection l E Y n).app ((rpush l E f).obj M)) δ) ∧
        IsIso (piComparison (rpushModule l E f) (fun n : ℕ ↦ (dev l E X n).obj M)) ∧
        (rpushModule l E f).map
            (towerTransitionEndomorphism (fun n : ℕ ↦ (transition l E X n).app M)) ≫
            piComparison (rpushModule l E f) (fun n : ℕ ↦ (dev l E X n).obj M) =
          piComparison (rpushModule l E f) (fun n : ℕ ↦ (dev l E X n).obj M) ≫
            towerTransitionEndomorphism
              (fun n : ℕ ↦ (rpushModule l E f).map ((transition l E X n).app M)) ∧
        ∀ n : ℕ, (pushLimitIso l E f).hom.app M ≫
            (levelProjection l E Y n).app ((rpush l E f).obj M) ≫
            (pushEvaluationMap l E f n).app M =
          (rpushModule l E f).map ((levelProjection l E X n).app M)) ∧
    IsIso (pushReductionMap l E f) ∧
    (∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      (rpushModule l E f).map ((kappa l E X).app K) ≫
          (pushLimitIso l E f).hom.app ((red l E X).obj K) =
        (kappa l E Y).app ((rpushModule l E f).obj K) ≫
          (rlim l E Y).map ((pushReductionMap l E f).app K)) ∧
    (∀ K : DerivedCategory (AdicCompletion.Modules l E X),
      IsDerivedComplete l E X K →
        IsDerivedComplete l E Y ((rpushModule l E f).obj K) ∧
        Nonempty ((rpushModule l E f).obj K ≅
          (rlim l E Y).obj ((rpush l E f).obj ((red l E X).obj K)))) := by
  have hroos := directImage_roos_limit_data l E f
  have hcomp := directImage_completion_compatibility l E f
  exact ⟨hroos.1, hroos.2, pushReductionMap_isIso l E f, hcomp.2.1, hcomp.2.2⟩

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
