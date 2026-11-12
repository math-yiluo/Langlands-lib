import Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinatePointTopologyFacts

/-! # Open maps for coordinate point topologies -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {C : Type u} [CommRing C] {ι : Type*}
  (R L : ι → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)]
  [∀ i, Field (L i)] [∀ i, Algebra C (L i)] [∀ i, TopologicalSpace (L i)]
  {A : Type u} [CommRing A] [Algebra C A]
  (φ : ∀ i, R i →ₐ[C] L i) (π : ∀ i, A →ₐ[C] R i)

/-- A bijective coordinate point map, with its defining induced topology, as an explicit
homeomorphism onto the product of the local point spaces. -/
def coordinatePointHomeomorph (X : AlgebraicSpace (Spec (CommRingCat.of C)))
    (hX : Function.Bijective (coordinatePointMap C X R π)) :
    @Homeomorph (RingPoints C X A) (∀ i, RingPoints C X (R i))
      (coordinatePointTopology C X R L φ π) (coordinateProductTopology C X R L φ) :=
  letI := coordinatePointTopology C X R L φ π
  letI := coordinateProductTopology C X R L φ
  (CoordinatePointTopologyFacts.isHomeomorph_coordinatePointMap X R L φ π hX).homeomorph
    (coordinatePointMap C X R π)

/-- Coordinate point maps commute with maps of algebraic spaces. -/
theorem coordinatePointMap_map
    {X Y : AlgebraicSpace (Spec (CommRingCat.of C))} (f : X ⟶ Y)
    (p : RingPoints C X A) (i : ι) :
    coordinatePointMap C Y R π (RingPoints.map f p) i =
      RingPoints.map f (coordinatePointMap C X R π p i) :=
  RingPoints.changeRing_map f (π i) p

/-- Local openness and surjectivity at all but finitely many coordinates imply openness
for the coordinate topologies whenever the coordinate maps are bijective. -/
theorem isOpenMap_coordinatePointMap_of_local
    {X Y : AlgebraicSpace (Spec (CommRingCat.of C))} (f : X ⟶ Y)
    (hX : Function.Bijective (coordinatePointMap C X R π))
    (hY : Function.Bijective (coordinatePointMap C Y R π))
    (ho : ∀ i, @IsOpenMap _ _ (fieldValuedPointTopology C X (φ i))
      (fieldValuedPointTopology C Y (φ i)) (RingPoints.map f))
    (hs : ∀ᶠ i in Filter.cofinite,
      Function.Surjective (RingPoints.map (A := R i) f)) :
    @IsOpenMap _ _ (coordinatePointTopology C X R L φ π)
      (coordinatePointTopology C Y R L φ π) (RingPoints.map f) := by
  let := coordinatePointTopology C X R L φ π
  let := coordinatePointTopology C Y R L φ π
  let : ∀ i, TopologicalSpace (RingPoints C X (R i)) :=
    fun i => fieldValuedPointTopology C X (φ i)
  let : ∀ i, TopologicalSpace (RingPoints C Y (R i)) :=
    fun i => fieldValuedPointTopology C Y (φ i)
  let eX := coordinatePointHomeomorph R L φ π X hX
  let eY := coordinatePointHomeomorph R L φ π Y hY
  have hprod : IsOpenMap (fun p : ∀ i, RingPoints C X (R i) =>
      fun i => RingPoints.map f (p i)) :=
    IsOpenMap.piMap (A := fun i => RingPoints C X (R i))
      (B := fun i => RingPoints C Y (R i)) ho hs
  apply eY.comp_isOpenMap_iff.mp
  have hn : eY ∘ RingPoints.map (A := A) f =
      (fun p : ∀ i, RingPoints C X (R i) => fun i => RingPoints.map f (p i)) ∘ eX := by
    funext p i
    exact coordinatePointMap_map R π f p i
  rw [hn]
  exact hprod.comp eX.isOpenMap

end Langlands.AlgebraicGeometry.AlgebraicSpace
