import Langlands.AlgebraicGeometry.PointTopology.FilteredRingPointTopology
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Open stages of the actual point colimit

The open continuous transition maps may be noninjective. Their actual images
carry the quotient topologies already constructed from the stages.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- Open continuous transitions give open stage maps and open quotient-topologized
stage images. Injective transitions additionally give open stage embeddings. -/
def FilteredRingPointOpenStages : Prop :=
  ∀ (R : Type u) [CommRing R] (J : Type u) [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) (X : Over (Spec (CommRingCat.of R)))
    (τ : ∀ j : J, TopologicalSpace (RingPoint R X (F.obj j))),
    (∀ (i j : J) (f : i ⟶ j),
      Continuous[τ i, τ j]
        (fun p : RingPoint R X (F.obj i) => p.changeRing (F.map f).hom) ∧
      @IsOpenMap _ _ (τ i) (τ j)
        (fun p : RingPoint R X (F.obj i) => p.changeRing (F.map f).hom)) →
    (∀ i : J, @IsOpenMap _ _ (τ i) (ringPointColimitTopology R F X τ)
      (ringPointColimitι R F X i)) ∧
    (∀ i : J, @IsOpenEmbedding _ _
      (ringPointColimitStageImageTopology R F X τ i) (ringPointColimitTopology R F X τ)
      (fun p : RingPointColimitStageImage R F X i => p.val)) ∧
    ((∀ (i j : J) (f : i ⟶ j), Function.Injective
      (fun p : RingPoint R X (F.obj i) => p.changeRing (F.map f).hom)) →
      ∀ i : J, @IsOpenEmbedding _ _ (τ i) (ringPointColimitTopology R F X τ)
        (ringPointColimitι R F X i))

end Langlands.AlgebraicGeometry.PointTopology
