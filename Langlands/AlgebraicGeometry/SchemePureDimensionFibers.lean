import Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-! # The pure-dimension component of the geometric fibre property -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Every actual residue-field fibre has pure dimension `d`.
Empty fibres satisfy this condition vacuously. -/
def HasPureDimensionFibers (d : ℕ) : MorphismProperty Scheme.{u} :=
  fun _ _ f => ∀ y, HasPureDimension (f.fiber y) d

variable {W X Y Z : Scheme.{u}} {d : ℕ}

/-- Restriction of the source isomorphism identifies the actual fibre spaces. -/
noncomputable def precompFiberHomeomorph (e : X ≅ Y) (f : Y ⟶ Z) (z : Z) :
    (e.hom ≫ f).fiber z ≃ₜ f.fiber z :=
  ((e.hom ≫ f).fiberHomeo z).trans
    ((e.schemeIsoToHomeo.subtype (by intro x; rfl)).trans (f.fiberHomeo z).symm)

/-- A target isomorphism transports a fibre to the inverse-image point. -/
noncomputable def postcompFiberHomeomorph (e : Y ≅ Z) (f : X ⟶ Y) (z : Z) :
    (f ≫ e.hom).fiber z ≃ₜ f.fiber (e.inv z) :=
  ((f ≫ e.hom).fiberHomeo z).trans
    ((Homeomorph.setCongr (by
      ext x
      exact e.schemeIsoToHomeo.eq_symm_apply.symm)).trans
        (f.fiberHomeo (e.inv z)).symm)

instance : (HasPureDimensionFibers d).RespectsIso :=
  MorphismProperty.RespectsIso.mk _
    (fun e f hf z => (hf z).of_homeomorph (precompFiberHomeomorph e f z).symm)
    (fun e f hf z => (hf (e.inv z)).of_homeomorph
      (postcompFiberHomeomorph e f z).symm)

/-- The full geometric fibre property factors into geometric connectedness
and its componentwise dimension condition. -/
theorem nonemptyGeometricallyConnectedPureDimensionFibers_eq :
    @(NonemptyGeometricallyConnectedPureDimensionFibers d) =
      (@GeometricallyConnected ⊓ @(HasPureDimensionFibers d) : MorphismProperty Scheme.{u}) := by
  ext X Y f
  exact nonemptyGeometricallyConnectedPureDimensionFibers_iff f

instance : (NonemptyGeometricallyConnectedPureDimensionFibers.{u} d).RespectsIso := by
  let : MorphismProperty.RespectsIso
      (@GeometricallyConnected : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [nonemptyGeometricallyConnectedPureDimensionFibers_eq]
  exact MorphismProperty.RespectsIso.inf
    (@GeometricallyConnected : MorphismProperty Scheme.{u}) (HasPureDimensionFibers d)

/-- Pure-dimensional fibres are invariant under an isomorphism of arrows. -/
theorem hasPureDimensionFibers_iff_of_arrow_iso {f : W ⟶ X} {g : Y ⟶ Z}
    (e : Arrow.mk f ≅ Arrow.mk g) :
    HasPureDimensionFibers d f ↔ HasPureDimensionFibers d g :=
  MorphismProperty.arrow_mk_iso_iff _ e

/-- The full geometric fibre property is invariant under an isomorphism of arrows. -/
theorem nonemptyGeometricallyConnectedPureDimensionFibers_iff_of_arrow_iso
    {f : W ⟶ X} {g : Y ⟶ Z} (e : Arrow.mk f ≅ Arrow.mk g) :
    NonemptyGeometricallyConnectedPureDimensionFibers d f ↔
      NonemptyGeometricallyConnectedPureDimensionFibers d g :=
  MorphismProperty.arrow_mk_iso_iff _ e

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
