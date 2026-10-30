import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation
import Langlands.AlgebraicGeometry.Picard.LineBundleTensor
import Langlands.AlgebraicGeometry.Modules.TensorSections
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof

/-! # Vanishing of line-bundle sections along field points and tangent vectors -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules

/-- Field-point tests and cancellation by factors generating along morphisms or tangents. -/
def LineBundleSectionVanishingStatement : Prop :=
  (∀ (X : Scheme.{u}) (F : Type u) [Field F] (L : LineBundle X)
      (x : Spec (CommRingCat.of F) ⟶ X) (s : GlobalSections L.obj)
      (y : Spec (CommRingCat.of F)),
    VanishesAlong L x s ↔ x y ∉ trivializationOpen L.obj s) ∧
  (∀ (X : Scheme.{u}) (F : Type u) [Field F] (L M : LineBundle X)
      (x : Spec (CommRingCat.of F) ⟶ X) (s : GlobalSections L.obj)
      (t : GlobalSections M.obj),
    VanishesAlong (LineBundle.tensor pullbackTensorComparisonIsIso L M) x
      (tensorSection L.obj M.obj s t) ↔ VanishesAlong L x s ∨ VanishesAlong M x t) ∧
  (∀ (X Y : Scheme.{u}) (L M : LineBundle X) (s : GlobalSections L.obj)
      (t : GlobalSections M.obj) (f : Y ⟶ X),
    (∀ y, f y ∈ trivializationOpen M.obj t) →
      (VanishesAlong (LineBundle.tensor pullbackTensorComparisonIsIso L M) f
        (tensorSection L.obj M.obj s t) ↔ VanishesAlong L f s)) ∧
  (∀ (X Y : Scheme.{u}) (L M : LineBundle X) (s : GlobalSections L.obj)
      (t : GlobalSections M.obj) (f : Y ⟶ X),
    (∀ y, f y ∈ trivializationOpen L.obj s) →
      (VanishesAlong (LineBundle.tensor pullbackTensorComparisonIsIso L M) f
        (tensorSection L.obj M.obj s t) ↔ VanishesAlong M f t)) ∧
  (∀ (K : Type u) [Field K] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of K))
      (x : Spec (CommRingCat.of K) ⟶ X)
      (v : Spec (CommRingCat.of (DualNumber K)) ⟶ X) (M : LineBundle X)
      (t : GlobalSections M.obj),
    IsTangentVectorAt p x v → ¬ VanishesAlong M x t →
      ∀ y, v y ∈ trivializationOpen M.obj t) ∧
  (∀ (K : Type u) [Field K] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of K))
      (x : Spec (CommRingCat.of K) ⟶ X)
      (v : Spec (CommRingCat.of (DualNumber K)) ⟶ X) (L M : LineBundle X)
      (s : GlobalSections L.obj) (t : GlobalSections M.obj),
    IsTangentVectorAt p x v → ¬ VanishesAlong M x t →
      (VanishesAlong (LineBundle.tensor pullbackTensorComparisonIsIso L M) v
        (tensorSection L.obj M.obj s t) ↔ VanishesAlong L v s)) ∧
  (∀ (K : Type u) [Field K] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of K))
      (x : Spec (CommRingCat.of K) ⟶ X)
      (v : Spec (CommRingCat.of (DualNumber K)) ⟶ X) (L M : LineBundle X)
      (s : GlobalSections L.obj) (t : GlobalSections M.obj),
    IsTangentVectorAt p x v → ¬ VanishesAlong L x s →
      (VanishesAlong (LineBundle.tensor pullbackTensorComparisonIsIso L M) v
        (tensorSection L.obj M.obj s t) ↔ VanishesAlong M v t))

end Langlands.AlgebraicGeometry.Picard
