/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.CompletePullbackReduction
import WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.AlgebraicGeometry.CompleteDerivedCompletion.DirectImageConeTowerStrictness

/-! # Finite levels of the direct-image reduction mate

Source: literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/prop-weil-pbc-direct-image-limits.proof.md, proof (2).
(blueprint: lem-weil-pbc-direct-image-completion-compatibility-levelwise-iso)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject
  AdicCompletion.ringCommutative AdicCompletion.modulesDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Every finite reduction evaluation of the direct-image reduction mate is an isomorphism.

Source: proof (2) of proposition-proper-base-change-complete-integral--1 (blueprint latest), Stacks
Tag 0944.

Proof. Fix `K` and `n`, and represent `K` by a K-injective complex `I`. Write
`B_n = [O_{E,Y} --π_E^n--> O_{E,Y}]` in degrees `-1, 0`, a bounded split-free complex
with `f^*B_n = [O_{E,X} --π_E^n--> O_{E,X}]`. By proposition-proper-base-change-complete-integral
and lemma-reduction-derived-nakayama--1, `dev n (red K)` is computed by `I ⊗ f^*B_n`, and by
lem-weil-pbc-split-perfect-tensor-kinjective this complex is again K-injective, so
`dev n (rpush (red K))` is computed by `f_*(I ⊗ f^*B_n)` (the evaluation comparison `β n` of
proposition-proper-base-change-complete-integral). On the other side `dev n (red (Rf_* K))` is
computed by `f_*I ⊗ B_n`. The strict cone-tower comparison
lem-weil-pbc-direct-image-cone-tower-strictness identifies `f_*I ⊗ B_n` with `f_*(I ⊗ f^*B_n)`
degreewise (additivity of `f_*` on the two summands of the cone), and its K-injective normalization
says that this strict isomorphism descends, through the unit/counit description of `β n` and of
`pullReduction` (lemma-weil-pbc-completed-pullback-reduction), to the level-`n` component of the
mate of `pullReduction`. Hence that component is an isomorphism.
(blueprint: lem-weil-pbc-direct-image-completion-compatibility-levelwise-iso) -/
theorem directImage_pushReductionMap_levelwiseIso :
    ∀ K : DerivedCategory (AdicCompletion.Modules l E X), ∀ n : ℕ,
      IsIso ((CompleteDerivedCompletion.dev l E Y n).map
        (((mateEquiv (moduleAdjunction l E f) (towerAdjunction l E f)
          (.mk _ _ _ _ (pullReduction l E f).hom))).app K)) := by
  sorry

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
