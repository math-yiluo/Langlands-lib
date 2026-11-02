import Langlands.AlgebraicGeometry.PointTopology.ProductRingPointComparisonStatement

/-!
# Proof of the relative product-ring point comparison

Reuse Mathlib's product-point theorems and prove the required relative
base-compatibility equation for the surjective lifts.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (C : Type u) [CommRing C] {ι : Type u} (R : ι → Type u)
variable [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)]
variable (X : Over (Spec (CommRingCat.of C)))

theorem productPointMap_injective [QuasiSeparatedSpace X.left] :
    Function.Injective (productPointMap C R X) := by
  intro p q h
  apply RingPoint.ext
  apply _root_.AlgebraicGeometry.pointsPi_injective
    (fun i => CommRingCat.of (R i)) X.left
  exact congrArg (fun x => fun i => (x i).left) h

private theorem productPointLift_base
    (x : ∀ i, RingPoint C X (R i))
    (f : Spec (CommRingCat.of (∀ i, R i)) ⟶ X.left)
    (hf : _root_.AlgebraicGeometry.pointsPi (fun i => CommRingCat.of (R i)) X.left f =
      fun i => (x i).left) :
    f ≫ X.hom = Spec.algebraMap C (∀ i, R i) := by
  apply _root_.AlgebraicGeometry.pointsPi_injective
    (fun i => CommRingCat.of (R i)) (Spec (CommRingCat.of C))
  funext i
  have hfi : Spec.map (CommRingCat.ofHom (Pi.evalRingHom R i)) ≫ f = (x i).left :=
    congrFun hf i
  change Spec.map (CommRingCat.ofHom (Pi.evalRingHom R i)) ≫ (f ≫ X.hom) =
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom R i)) ≫ Spec.algebraMap C (∀ i, R i)
  rw [← Category.assoc, hfi]
  exact (Over.w (x i)).trans (Over.w (ringTestMap C (Pi.evalAlgHom C R i))).symm

private theorem productPointMap_surjective_of_underlying
    (h : Function.Surjective
      (_root_.AlgebraicGeometry.pointsPi (fun i => CommRingCat.of (R i)) X.left)) :
    Function.Surjective (productPointMap C R X) := by
  intro x
  obtain ⟨f, hf⟩ := h (fun i => (x i).left)
  refine ⟨Over.homMk f (productPointLift_base C R X x f hf), ?_⟩
  funext i
  apply RingPoint.ext
  exact congrFun hf i

theorem productPointMap_surjective_of_isAffine [IsAffine X.left] :
    Function.Surjective (productPointMap C R X) :=
  productPointMap_surjective_of_underlying C R X
    (_root_.AlgebraicGeometry.pointsPi_surjective_of_isAffine
      (fun i => CommRingCat.of (R i)) X.left)

theorem productPointMap_surjective [CompactSpace X.left] [∀ i, IsLocalRing (R i)] :
    Function.Surjective (productPointMap C R X) :=
  productPointMap_surjective_of_underlying C R X
    (_root_.AlgebraicGeometry.pointsPi_surjective
      (fun i => CommRingCat.of (R i)) X.left)

/-- The exact three-clause source-qualified product-ring point comparison. -/
theorem productRingPointComparison : ProductRingPointComparisonStatement.{u} := by
  intro C _ ι R _ _ X
  refine ⟨?_, ?_, ?_⟩
  · intro hQS
    exact productPointMap_injective C R X
  · intro hAffine
    exact productPointMap_surjective_of_isAffine C R X
  · intro hCompact hLocal
    exact productPointMap_surjective C R X

end Langlands.AlgebraicGeometry.PointTopology
