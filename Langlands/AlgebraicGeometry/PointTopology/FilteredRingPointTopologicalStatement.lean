import Langlands.AlgebraicGeometry.PointTopology.FilteredRingPointStatement
import Langlands.AlgebraicGeometry.PointTopology.FilteredRingPointOpenStatement
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Separation.Hausdorff

/-!
# Final-topology comparison for actual filtered scheme points

Local finite presentation supplies the point bijection. The topologies are
specified independently, and openness and the further topological properties
retain their separate stage hypotheses.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The actual finite-presentation homeomorphism, open stage maps, local
compactness, countable-cover second countability, and the injective Hausdorff case. -/
def FilteredRingPointTopologicalComparison : Prop :=
  ∀ (R : Type u) [CommRing R] (J : Type u) [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) (c : Cocone F) (_hc : IsColimit c)
    (X : Over (Spec (CommRingCat.of R))) (_hfp : LocallyOfFinitePresentation X.hom)
    (τ : ∀ j : J, TopologicalSpace (RingPoint R X (F.obj j))),
    (∃ e : @Homeomorph (RingPointColimit R F X) (RingPoint R X c.pt)
        (ringPointColimitTopology R F X τ) (ringPointCoconeTopology R F X τ c),
      ∀ p, e p = ringPointColimitMap R F X c p) ∧
    ((∀ (i j : J) (f : i ⟶ j),
        Continuous[τ i, τ j]
          (fun p : RingPoint R X (F.obj i) => p.changeRing (F.map f).hom) ∧
        @IsOpenMap _ _ (τ i) (τ j)
          (fun p : RingPoint R X (F.obj i) => p.changeRing (F.map f).hom)) →
      (∀ i : J, @IsOpenMap _ _ (τ i) (ringPointCoconeTopology R F X τ c)
        (fun p : RingPoint R X (F.obj i) => p.changeRing (c.ι.app i).hom)) ∧
      ((∀ i : J, @LocallyCompactSpace _ (τ i)) →
        @LocallyCompactSpace _ (ringPointCoconeTopology R F X τ c)) ∧
      (∀ (S : Set J), S.Countable →
        (∀ p : RingPoint R X c.pt,
          ∃ i ∈ S, ∃ q : RingPoint R X (F.obj i), q.changeRing (c.ι.app i).hom = p) →
        (∀ i ∈ S, @SecondCountableTopology _ (τ i)) →
        @SecondCountableTopology _ (ringPointCoconeTopology R F X τ c)) ∧
      ((∀ (i j : J) (f : i ⟶ j), Function.Injective
          (fun p : RingPoint R X (F.obj i) => p.changeRing (F.map f).hom)) →
        (∀ i : J, @IsOpenEmbedding _ _ (τ i) (ringPointCoconeTopology R F X τ c)
          (fun p : RingPoint R X (F.obj i) => p.changeRing (c.ι.app i).hom)) ∧
        ((∀ i : J, @T2Space _ (τ i)) →
          @T2Space _ (ringPointCoconeTopology R F X τ c))))

end Langlands.AlgebraicGeometry.PointTopology
