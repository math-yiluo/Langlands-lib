import Langlands.AlgebraicGeometry.SchemeFiberBaseChange
import Langlands.AlgebraicGeometry.GeometricallyConnectedDescent

/-! # Actual geometric fibre loci and their elementary comparisons -/

universe u

open Set CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

variable {X Y : Scheme.{u}}

/-- Target points with nonempty actual residue-field fibre. -/
def nonemptyFiberLocus (f : X ⟶ Y) : Set Y :=
  {y | Nonempty (f.fiber y)}

/-- Target points with geometrically connected actual residue-field fibre. -/
def geometricallyConnectedFiberLocus (f : X ⟶ Y) : Set Y :=
  {y | GeometricallyConnected (f.fiberToSpecResidueField y)}

/-- Target points whose actual fibre is componentwise pure-dimensional. -/
def pureDimensionFiberLocus (d : ℕ) (f : X ⟶ Y) : Set Y :=
  {y | HasPureDimension (f.fiber y) d}

/-- The exact pointwise conjunction in Conrad's last fibre-property clause. -/
def nonemptyGeometricallyConnectedPureDimensionFiberLocus (d : ℕ) (f : X ⟶ Y) : Set Y :=
  {y | Nonempty (f.fiber y) ∧ GeometricallyConnected (f.fiberToSpecResidueField y) ∧
    HasPureDimension (f.fiber y) d}

/-- Nonemptiness is measured on scheme fibres, and equals the actual map image. -/
theorem nonemptyFiberLocus_eq_range (f : X ⟶ Y) :
    nonemptyFiberLocus f = range f := by
  ext y
  constructor
  · rintro ⟨x⟩
    exact ⟨_, ((f.fiberHomeo y) x).2⟩
  · rintro ⟨x, hx⟩
    exact ⟨(f.fiberHomeo y).symm ⟨x, hx⟩⟩

/-- Geometric connectedness includes nonemptiness in Mathlib's convention. -/
theorem geometricallyConnectedFiberLocus_subset_nonemptyFiberLocus (f : X ⟶ Y) :
    geometricallyConnectedFiberLocus f ⊆ nonemptyFiberLocus f := by
  intro y hy
  let : GeometricallyConnected (f.fiberToSpecResidueField y) := hy
  let : ConnectedSpace (f.fiber y) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f.fiberToSpecResidueField y)
  change Nonempty (f.fiber y)
  exact inferInstance

/-- The explicit nonempty conjunct is redundant but remains in the original locus. -/
theorem nonemptyGeometricallyConnectedPureDimensionFiberLocus_eq (d : ℕ) (f : X ⟶ Y) :
    nonemptyGeometricallyConnectedPureDimensionFiberLocus d f =
      geometricallyConnectedFiberLocus f ∩ pureDimensionFiberLocus d f := by
  ext y
  exact ⟨fun h => h.2, fun h =>
    ⟨geometricallyConnectedFiberLocus_subset_nonemptyFiberLocus f h.1, h⟩⟩

/-- Fullness of the actual locus is the original all-fibres property. -/
theorem nonemptyGeometricallyConnectedPureDimensionFiberLocus_eq_univ_iff
    (d : ℕ) (f : X ⟶ Y) :
    nonemptyGeometricallyConnectedPureDimensionFiberLocus d f = univ ↔
      NonemptyGeometricallyConnectedPureDimensionFibers d f :=
  eq_univ_iff_forall

/-- Fullness of the dimension locus is the original all-fibres dimension condition. -/
theorem pureDimensionFiberLocus_eq_univ_iff (d : ℕ) (f : X ⟶ Y) :
    pureDimensionFiberLocus d f = univ ↔ HasPureDimensionFibers d f :=
  eq_univ_iff_forall

/-- Fullness of the geometric-connectedness locus uses Mathlib's exact fibre criterion. -/
theorem geometricallyConnectedFiberLocus_eq_univ_iff (f : X ⟶ Y) :
    geometricallyConnectedFiberLocus f = univ ↔ GeometricallyConnected f :=
  eq_univ_iff_forall.trans (GeometricallyConnected.iff_geometricallyConnected_fiber f).symm

variable {P Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
  {f : X ⟶ Z} {g : Y ⟶ Z}

/-- Every actual residue-field extension is surjective on spectra. -/
theorem surjective_spec_residueFieldMap (g : Y ⟶ Z) (y : Y) :
    Surjective (Spec.map (g.residueFieldMap y)) :=
  ⟨Function.surjective_to_subsingleton _⟩

/-- Fibre nonemptiness is preserved and reflected at each point of any base change. -/
theorem nonempty_fiberBaseChange_iff (h : IsPullback a b f g) (y : Y) :
    Nonempty (b.fiber y) ↔ Nonempty (f.fiber (g y)) := by
  have : Surjective (Spec.map (g.residueFieldMap y)) := surjective_spec_residueFieldMap g y
  have hsurj : Surjective (fiberBaseChangeMap h y) :=
    MorphismProperty.of_isPullback (fiberBaseChangeSquare h y).flip inferInstance
  constructor
  · exact Nonempty.map (fiberBaseChangeMap h y)
  · rintro ⟨x⟩
    obtain ⟨z, _⟩ := hsurj.surj x
    exact ⟨z⟩

/-- Geometric connectedness is preserved and reflected along the actual residue-field map. -/
theorem geometricallyConnected_fiberBaseChange_iff (h : IsPullback a b f g) (y : Y) :
    GeometricallyConnected (b.fiberToSpecResidueField y) ↔
      GeometricallyConnected (f.fiberToSpecResidueField (g y)) := by
  have : Surjective (Spec.map (g.residueFieldMap y)) := surjective_spec_residueFieldMap g y
  constructor
  · intro hb
    let := hb
    exact Langlands.AlgebraicGeometry.geometricallyConnected_of_surjective_isPullback
      _ _ (fiberBaseChangeSquare h y)
  · intro hf
    exact MorphismProperty.of_isPullback (fiberBaseChangeSquare h y) hf

/-- Nonemptiness loci commute with arbitrary cartesian base change. -/
theorem nonemptyFiberLocus_baseChange (h : IsPullback a b f g) :
    nonemptyFiberLocus b = g ⁻¹' nonemptyFiberLocus f := by
  ext y
  exact nonempty_fiberBaseChange_iff h y

/-- Geometric-connectedness loci commute with arbitrary cartesian base change. -/
theorem geometricallyConnectedFiberLocus_baseChange (h : IsPullback a b f g) :
    geometricallyConnectedFiberLocus b = g ⁻¹' geometricallyConnectedFiberLocus f := by
  ext y
  exact geometricallyConnected_fiberBaseChange_iff h y

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
