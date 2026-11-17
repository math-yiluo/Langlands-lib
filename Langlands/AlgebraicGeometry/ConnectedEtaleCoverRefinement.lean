import Langlands.AlgebraicGeometry.PointedConnectedComponentGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Connected refinements of étale covers over local spectra -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- An open map to a local spectrum is surjective if its image contains the
closed point. -/
theorem surjective_of_isOpenMap_of_closedPoint_mem
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (hf : IsOpenMap f)
    (hclosed : IsLocalRing.closedPoint R ∈ Set.range f) : Surjective f := by
  refine ⟨fun y => ?_⟩
  exact (IsLocalRing.specializes_closedPoint y).mem_open hf.isOpen_range hclosed

/-- The connected component through a point over the closed point of a local
spectrum still maps surjectively, provided the original map is open. -/
theorem connectedComponentOpen_surjective_of_closedPoint
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of R)) (hf : IsOpenMap f)
    (x : X) (hx : f x = IsLocalRing.closedPoint R) :
    Surjective ((connectedComponentOpen X x).ι ≫ f) := by
  apply surjective_of_isOpenMap_of_closedPoint_mem
  · exact hf.comp (connectedComponentOpen X x).ι.isOpenEmbedding.isOpenMap
  · refine ⟨⟨x, mem_connectedComponent⟩, ?_⟩
    exact hx

/-- Every étale surjection onto a Noetherian local spectrum has a connected
open refinement which remains an étale surjection. -/
theorem exists_connected_etale_refinement
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) [Etale f] [Surjective f] :
    ∃ (V : X.Opens), ConnectedSpace V ∧ Etale (V.ι ≫ f) ∧ Surjective (V.ι ≫ f) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨x, hx⟩ := f.surjective (IsLocalRing.closedPoint R)
  refine ⟨connectedComponentOpen X x, inferInstance, inferInstance, ?_⟩
  exact connectedComponentOpen_surjective_of_closedPoint f f.isOpenMap x hx

/-- A chosen connected open refinement of an étale cover of a Noetherian
local spectrum. -/
def connectedEtaleRefinementOpen
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) [Etale f] [Surjective f] : X.Opens :=
  (exists_connected_etale_refinement R X f).choose

instance connectedSpace_connectedEtaleRefinementOpen
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) [Etale f] [Surjective f] :
    ConnectedSpace (connectedEtaleRefinementOpen R X f) :=
  (exists_connected_etale_refinement R X f).choose_spec.1

instance etale_connectedEtaleRefinementOpen
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) [Etale f] [Surjective f] :
    Etale ((connectedEtaleRefinementOpen R X f).ι ≫ f) :=
  (exists_connected_etale_refinement R X f).choose_spec.2.1

instance surjective_connectedEtaleRefinementOpen
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) [Etale f] [Surjective f] :
    Surjective ((connectedEtaleRefinementOpen R X f).ι ≫ f) :=
  (exists_connected_etale_refinement R X f).choose_spec.2.2

end Langlands.AlgebraicGeometry
