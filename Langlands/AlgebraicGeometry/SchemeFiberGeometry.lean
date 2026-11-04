import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.Topology.KrullDimension

/-! # Pure-dimensional residue-field fibres of actual scheme morphisms -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Every irreducible component, with its subspace topology, has dimension `d`.
The empty scheme satisfies this condition vacuously. -/
def HasPureDimension (X : Scheme.{u}) (d : ℕ) : Prop :=
  ∀ Z : Set X, Z ∈ irreducibleComponents X →
    topologicalKrullDim Z = (d : WithBot ℕ∞)

/-- The last property in Conrad's Theorem 3.4(2), on actual residue-field
fibres. Nonemptiness is explicit, even though geometric connectedness implies it. -/
def NonemptyGeometricallyConnectedPureDimensionFibers (d : ℕ) :
    MorphismProperty Scheme.{u} :=
  fun _ _ f => ∀ y, Nonempty (f.fiber y) ∧
    GeometricallyConnected (f.fiberToSpecResidueField y) ∧
    HasPureDimension (f.fiber y) d

variable {X Y : Scheme.{u}} {d : ℕ}

/-- Pure dimension depends only on the underlying topological space. -/
theorem HasPureDimension.of_homeomorph (h : HasPureDimension X d) (e : X ≃ₜ Y) :
    HasPureDimension Y d := by
  intro Z hZ
  have hpre : e ⁻¹' Z ∈ irreducibleComponents X :=
    preimage_mem_irreducibleComponents hZ e.isOpenEmbedding
      (by simpa only [e.surjective.range_eq, Set.inter_univ] using hZ.1.1)
  let eZ : (e ⁻¹' Z) ≃ₜ Z :=
    (e.image (e ⁻¹' Z)).trans
      (Homeomorph.setCongr (Set.image_preimage_eq Z e.surjective))
  exact (eZ.isHomeomorph.topologicalKrullDim_eq _).symm.trans (h _ hpre)

/-- Scheme isomorphisms preserve pure dimension in both directions. -/
theorem hasPureDimension_iff_of_iso (e : X ≅ Y) :
    HasPureDimension X d ↔ HasPureDimension Y d :=
  ⟨fun h => h.of_homeomorph e.hom.homeomorph,
    fun h => h.of_homeomorph e.inv.homeomorph⟩

/-- Exact comparison with Mathlib's geometric-connectedness predicate.
The dimension condition remains componentwise on each actual fibre. -/
theorem nonemptyGeometricallyConnectedPureDimensionFibers_iff (f : X ⟶ Y) :
    NonemptyGeometricallyConnectedPureDimensionFibers d f ↔
      GeometricallyConnected f ∧ ∀ y, HasPureDimension (f.fiber y) d := by
  constructor
  · intro h
    exact ⟨(GeometricallyConnected.iff_geometricallyConnected_fiber f).mpr
      (fun y => (h y).2.1), fun y => (h y).2.2⟩
  · rintro ⟨hf, hd⟩
    let := hf
    exact fun y => ⟨inferInstance, inferInstance, hd y⟩

/-- The explicit fibre property implies surjectivity of the actual scheme map. -/
theorem NonemptyGeometricallyConnectedPureDimensionFibers.surjective
    {f : X ⟶ Y} (h : NonemptyGeometricallyConnectedPureDimensionFibers d f) :
    Surjective f := by
  let := (nonemptyGeometricallyConnectedPureDimensionFibers_iff f).mp h |>.1
  infer_instance

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
