/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Finite
import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-! # Exactness of closed direct image on coefficient systems

Source: Bhatt--Scholze, Lemma 6.1.17; blueprint classes clause (3).
(blueprint: lem-sp-closed-tower-direct-image-exact).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] sfIntrinsicModuleEquivalence

private theorem constantRingPushforward_exact
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [LocallyOfFinitePresentation f] :
    PreservesFiniteLimits (proEtaleConstantRingPushforward A f) ∧
      PreservesFiniteColimits (proEtaleConstantRingPushforward A f) := by
  have : PreservesFiniteLimits (proEtaleConstantRingPushforward A
      f) := by
    have := (proEtaleConstantRingAdjunction A f).isRightAdjoint
    infer_instance
  refine ⟨inferInstance, ?_⟩
  let eT := sfIntrinsicModuleEquivalence Y A
  let eZ := sfIntrinsicModuleEquivalence X A
  let ai := upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A))
    f
  let ai' := (eT.symm.toAdjunction.comp ai).comp eZ.toAdjunction
  let q := (ai'.ofNatIsoLeft
    (openSquarePullbackModel A f).symm).rightAdjointUniq
      (proEtaleConstantRingAdjunction A f)
  have := preservesFiniteColimits_lowerStar_of_isFinite (ULift.{u + 1} A)
    f
  have : PreservesFiniteColimits
      (eZ.inverse ⋙ lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A))
        f ⋙ eT.functor) := inferInstance
  exact preservesFiniteColimits_of_natIso q

/-- A closed immersion locally of finite presentation has exact ordinary system direct image.
Source: Bhatt--Scholze, Lemma 6.1.17, applied to each finite coefficient level.
(blueprint: lem-sp-closed-tower-direct-image-exact).

Proof: a closed immersion is finite. At each level, identify the intrinsic constant-ring
pushforward with fixed-scalar module-sheaf direct image through the coefficient equivalences
and uniqueness of right adjoints. Finite direct image preserves finite colimits, and its
adjunction supplies finite limits. System evaluation functors are exact and jointly faithful:
a morphism is determined at every pair consisting of a level and a chart. Their ordinary
pushforward comparison therefore detects exactness of the system direct image. Empty
schemes and the zero coefficient ring cause no exception. -/
theorem closedTowerPush_exact {b : SpTowerShriek.Base l E}
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] [LocallyOfFinitePresentation f]
    (g : SpTowerShriek.Geometry l E b f) :
    PreservesFiniteLimits g.push ∧ PreservesFiniteColimits g.push := by
  have hfaith : JointlyFaithful (SpTowerShriek.ev l E Y) := by
    constructor
    intro M N f h hfh
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    rintro ⟨n, V⟩
    ext x
    exact congrArg (fun k ↦ k.val.app (op V) x) (hfh n)
  apply hfaith.jointlyReflectsIsomorphisms.exactFunctor_of_iso g.push
    (fun n ↦ proEtaleConstantRingPushforward (SpTowerShriek.R l E n)
      f) _ g.ordinaryPushEvaluation
  intro n
  let : Finite (SpTowerShriek.R l E n) := b.finite n
  exact constantRingPushforward_exact (SpTowerShriek.R l E n) f

end AlgebraicGeometry.ProEtale.SpTowerClasses
