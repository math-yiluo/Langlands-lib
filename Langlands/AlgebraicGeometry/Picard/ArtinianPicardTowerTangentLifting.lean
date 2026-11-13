import Langlands.AlgebraicGeometry.Picard.ArtinianPicardTowerEvaluation
import Langlands.AlgebraicGeometry.Picard.ArtinianPicardTowerMaps
import Langlands.AlgebraicGeometry.Picard.ArtinianPicardTowerFamily
import Langlands.AlgebraicGeometry.Picard.ArtinianChartVersality
import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.ChartOpenness
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberAtlasRestriction
import Langlands.CategoryTheory.Sites.PseudofunctorPointFiberObjectIso

/-! # Lifting along the dual numbers for the effective Picard tower bundle -/

noncomputable section
universe u w₁ w₂ w₃ w₄
open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardTowerTangentLifting

open Langlands.AlgebraicGeometry.Deformation Langlands.CategoryTheory
open PseudofunctorPointFiber

section Generic

open CategoryTheory.Bicategory

variable {C : Type w₁} [Category.{w₂} C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{w₃, w₄})
  {U V S : C} (i : V ⟶ U) (ξ : F.obj (.mk (op U))) (η : F.obj (.mk (op S)))

/-- A point whose map to the atlas factors through `i` comes from a point of the restricted
atlas object with the given factor. -/
lemma exists_mapPoints_eq {Z : Over S} (x : Points F ξ η Z) (a : Z.left ⟶ V)
    (ha : a ≫ i = x.1) :
    ∃ z : Points F ((F.map i.op.toLoc).toFunctor.obj ξ) η Z, z.1 = a ∧
      PseudofunctorPointFiberAtlasRestriction.mapPoints F i ξ η Z z = x := by
  rcases x with ⟨b, e⟩
  dsimp only at ha
  subst ha
  exact ⟨⟨a, (PseudofunctorPointFiberAtlasRestriction.atlasComparison F i ξ a).symm ≪≫ e⟩,
    rfl, by simp [PseudofunctorPointFiberAtlasRestriction.mapPoints]⟩

end Generic

open ArtinianChartLifting ArtinianChartVersality

section Transfer

variable {k K : Type u} [CommRing k] [Field K] [Algebra k K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  {H : Type u} [CommRing H] [Algebra k H]
  (L : LineBundle ((relativeSpace f).obj (affineBase k H)))
  (p : ArtinianTest.residueBase k K ⟶ affineBase k H)
  {T₀ : ArtinianTest k K} (L₀ : LineBundle ((relativeSpace f).obj (ArtinianTest.base T₀)))
  (i : ArtinianTest.base T₀ ⟶ affineBase k H)

/-- Lifting along the dual numbers passes from a family `L₀` on a test `T₀` to a family `L`
whose pullback along `i` is `L₀`, when the closed point of `L` is the closed point of `T₀`
followed by `i`. -/
theorem hasLiftingForAt_dualReduction_of_pullback
    (hi : ArtinianTest.reduction T₀ ≫ i = p)
    (Φ : (LineBundle.pullback ((relativeSpace f).map i)).obj L ≅ L₀)
    (h₀ : HasLiftingForAt f L₀ (ArtinianTest.reduction T₀) (ArtinianTest.dualReduction k K)) :
    HasLiftingForAt f L p (ArtinianTest.dualReduction k K) := by
  intro T N a b w y hy
  let e : ((relative f).map i.op.toLoc).toFunctor.obj (Core.mk L) ≅ Core.mk L₀ := Core.isoMk Φ
  have hy₁ : ArtinianTest.reduction T₀ ≫ i = y.1 := by
    rw [hi, ← hy, reduction_residue, Category.id_comp]
  obtain ⟨z, hz₁, hz⟩ := exists_mapPoints_eq (relative f) (S := T) i (Core.mk L) (Core.mk N) y
    (ArtinianTest.reduction T₀) hy₁
  obtain ⟨x₀, hx₀⟩ := h₀ T N a b w
    (PseudofunctorPointFiberObjectIso.mapPoints (relative f) e (Core.mk N) _ z) (by
      change ArtinianTest.reduction (ArtinianTest.residue k K) ≫ z.1 = ArtinianTest.reduction T₀
      rw [hz₁, reduction_residue, Category.id_comp])
  refine ⟨PseudofunctorPointFiberAtlasRestriction.mapPoints (relative f) i (Core.mk L)
    (Core.mk N) _ (PseudofunctorPointFiberObjectIso.mapPoints (relative f) e.symm (Core.mk N) _ x₀),
    ?_⟩
  have hx₀' : PseudofunctorPointFiber.restrict (relative f) (Core.mk L₀) (Core.mk N)
      (testArrow (ArtinianTest.dualReduction k K) w) x₀ =
        PseudofunctorPointFiberObjectIso.mapPoints (relative f) e (Core.mk N) _ z := hx₀
  change PseudofunctorPointFiber.restrict (relative f) (Core.mk L) (Core.mk N)
      (testArrow (ArtinianTest.dualReduction k K) w)
      (PseudofunctorPointFiberAtlasRestriction.mapPoints (relative f) i (Core.mk L) (Core.mk N) _
        (PseudofunctorPointFiberObjectIso.mapPoints (relative f) e.symm (Core.mk N) _ x₀)) = y
  rw [← PseudofunctorPointFiberAtlasRestriction.mapPoints_restrict,
    ← PseudofunctorPointFiberObjectIso.mapPoints_restrict, hx₀',
    PseudofunctorPointFiberObjectIso.mapPoints_symm, hz]

end Transfer

section Effective

open ArtinianPicardSourceStep ArtinianPicardSourceTower ArtinianPicardTowerFormalSystem
open ArtinianPicardTowerAlgebraization ArtinianPicardTowerEvaluation ArtinianPicardTowerMaps

variable {k K R : Type u} [CommRing k] [Field K] [Algebra k K]
  [CommRing R] [Algebra k R] [IsLocalRing R] [IsNoetherianRing R]
  (ε : R →ₐ[k] K) (hε : Function.Surjective ε)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (M : LineBundle ((relativeSpace f).obj (ArtinianTest.residueBase k K)))
  [Flat f] [IsProper f] (s₀ : Stage ε f M)
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- The pullback of the effective bundle to the initial tower test is the initial bundle. -/
lemma nonempty_initialIso :
    Nonempty ((LineBundle.pullback ((relativeSpace f).map
      (affineBaseMap (projection ε hε f M s₀ 0)))).obj (effectiveBundle ε hε f M s₀) ≅
        ArtinianPicardTowerFamily.bundle ε hε f M s₀ 0) := by
  obtain ⟨a, ha⟩ := ArtinianAdicEvaluation.exists_bound
    (IsLocalRing.maximalIdeal (limitRing ε hε f M s₀)) (projection ε hε f M s₀ 0)
    (limitAugmentation ε hε f M s₀) (maximalIdeal_le_augmentation ε hε f M s₀)
    (augmentation_projection ε hε f M s₀ 0)
  have hg : stageMap ε hε f M s₀ (projection ε hε f M s₀ 0)
      (augmentation_projection ε hε f M s₀ 0) a ha =
        towerMap ε hε f M s₀ (Nat.zero_le (index ε hε f M s₀ a)) :=
    towerMap_unique ε hε f M s₀ _ _ (stageMap_projection ε hε f M s₀ _ _ a ha)
  obtain ⟨d⟩ := ArtinianPicardTowerFamily.hasTransition ε hε f M s₀
    (Nat.zero_le (index ε hε f M s₀ a))
  exact ⟨effectiveEvaluationIso ε hε f M s₀ (projection ε hε f M s₀ 0)
      (augmentation_projection ε hε f M s₀ 0) a ha ≪≫
    eqToIso (congrArg (fun t ↦ (LineBundle.pullback ((relativeSpace f).map
      (ArtinianTest.baseMap t))).obj
        (ArtinianPicardTowerFamily.bundle ε hε f M s₀ (index ε hε f M s₀ a))) hg) ≪≫ d⟩

/-- Lifting along the dual numbers for the effective bundle at its closed point, from
lifting along the dual numbers for the initial family at the closed point of its test. -/
theorem hasLiftingForAt_dualReduction
    (h₀ : HasLiftingForAt f s₀.family.right.of (ArtinianTest.reduction s₀.test)
      (ArtinianTest.dualReduction k K)) :
    HasLiftingForAt f (effectiveBundle ε hε f M s₀) (residuePoint ε hε f M s₀)
      (ArtinianTest.dualReduction k K) := by
  obtain ⟨Φ⟩ := nonempty_initialIso ε hε f M s₀
  refine hasLiftingForAt_dualReduction_of_pullback f (effectiveBundle ε hε f M s₀)
    (residuePoint ε hε f M s₀) (T₀ := test ε hε f M s₀ 0)
    (ArtinianPicardTowerFamily.bundle ε hε f M s₀ 0)
    (affineBaseMap (projection ε hε f M s₀ 0)) ?_ Φ h₀
  rw [OpennessOfVersality.reduction_comp_affineBaseMap, augmentation_projection]
  rfl

end Effective

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid.ArtinianPicardTowerTangentLifting
