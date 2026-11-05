import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Fibre components meeting a section -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SectionComponent

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (e : Y ⟶ X) (he : e ≫ f = 𝟙 Y)

/-- The residue-field-valued point of a fibre induced by a section. -/
def fiberSection (y : Y) : Spec (Y.residueField y) ⟶ f.fiber y :=
  pullback.lift (Y.fromSpecResidueField y ≫ e) (𝟙 _) (by simp [Category.assoc, he])

@[reassoc (attr := simp)]
theorem fiberSection_fiberι (y : Y) :
    fiberSection f e he y ≫ f.fiberι y = Y.fromSpecResidueField y ≫ e :=
  pullback.lift_fst ..

@[reassoc (attr := simp)]
theorem fiberSection_toSpec (y : Y) :
    fiberSection f e he y ≫ f.fiberToSpecResidueField y = 𝟙 _ :=
  pullback.lift_snd ..

/-- The point of a residue fibre selected by the section. -/
def fiberPoint (y : Y) : f.fiber y :=
  fiberSection f e he y (IsLocalRing.closedPoint (Y.residueField y))

@[simp]
theorem fiberι_fiberPoint (y : Y) :
    f.fiberι y (fiberPoint f e he y) = e y := by
  change (fiberSection f e he y ≫ f.fiberι y) _ = _
  rw [fiberSection_fiberι]
  change e (Y.fromSpecResidueField y _) = e y
  exact congrArg e (Scheme.fromSpecResidueField_apply y _)

/-- The projection of a fibre point lies over its indexing point. -/
theorem structure_fiberι (y : Y) (z : f.fiber y) :
    f (f.fiberι y z) = y :=
  (f.fiberHomeo y z).property

/-- The union of the connected components of the fibres meeting the section. -/
def componentSet : Set X :=
  {x | ∃ (y : Y) (z : f.fiber y),
    z ∈ connectedComponent (fiberPoint f e he y) ∧ f.fiberι y z = x}

/-- On each actual fibre, membership in the union is membership in its chosen component. -/
theorem fiberι_mem_componentSet_iff (y : Y) (z : f.fiber y) :
    f.fiberι y z ∈ componentSet f e he ↔
      z ∈ connectedComponent (fiberPoint f e he y) := by
  constructor
  · rintro ⟨y', z', hz', h⟩
    have hy : y' = y := by
      simpa only [structure_fiberι] using congrArg f h
    subst y'
    have hz : z' = z := (f.fiberι y).isEmbedding.injective h
    simpa only [hz] using hz'
  · intro hz
    exact ⟨y, z, hz, rfl⟩

/-- Every point of the section belongs to the union. -/
theorem section_mem_componentSet (y : Y) : e y ∈ componentSet f e he :=
  ⟨y, fiberPoint f e he y, mem_connectedComponent, fiberι_fiberPoint f e he y⟩

/-- The whole image of the section lies in the union. -/
theorem range_section_subset_componentSet : Set.range e ⊆ componentSet f e he := by
  rintro _ ⟨y, rfl⟩
  exact section_mem_componentSet f e he y

end Langlands.AlgebraicGeometry.SectionComponent
