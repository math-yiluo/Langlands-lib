import Langlands.AlgebraicGeometry.RelationEtaleSliceGlobalizationProof
import Langlands.AlgebraicGeometry.RelationSliceImageSaturationProof

/-! # Etale surjective slices from local slices on every orbit -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

open AlgebraicSpace.AtlasRelation

/-- A locally finite type slice with etale surjective associated map. -/
structure EtaleRelationSliceData {U R : Scheme.{u}} (t s : R ⟶ U) where
  scheme : Scheme.{u}
  toBase : scheme ⟶ U
  locallyOfFiniteType : LocallyOfFiniteType toBase
  etale : Etale (pullback.snd toBase t ≫ s)
  surjective : Surjective (pullback.snd toBase t ≫ s)

/-- Slices through one point in every orbit give a global etale surjective
slice. The predicate marking those points can be arbitrary. -/
theorem exists_etale_surjective_slice_of_orbit_slices
    {U R : Scheme.{u}} (t s : R ⟶ U) (hr : IsEquivRel t s)
    (P : U → Prop)
    (horbit : ∀ x : U, ∃ r : R, s r = x ∧ P (t r))
    (hslice : ∀ y : U, P y →
      ∃ (V : Scheme.{u}) (g : V ⟶ U), LocallyOfFiniteType g ∧
        Etale (pullback.snd g t ≫ s) ∧ y ∈ Set.range g) :
    ∃ (V : Scheme.{u}) (g : V ⟶ U), LocallyOfFiniteType g ∧
      Etale (pullback.snd g t ≫ s) ∧ Surjective (pullback.snd g t ≫ s) := by
  apply exists_etale_surjective_slice_of_finiteTypePoint_slices t s
  intro x _
  obtain ⟨r, hrx, hgood⟩ := horbit x
  obtain ⟨V, g, hfg, he, hy⟩ := hslice (t r) hgood
  refine ⟨V, g, hfg, he, ?_⟩
  rw [← hrx]
  exact mem_relation_slice_image_of_source_mem t s hr g r
    (range_subset_relation_slice_image t s hr g hy)

/-- Choose a global etale surjective slice from local slices through a
predicate satisfied by a point on every orbit. -/
def etaleRelationSliceOfOrbits
    {U R : Scheme.{u}} (t s : R ⟶ U) (hr : IsEquivRel t s)
    (P : U → Prop)
    (horbit : ∀ x : U, ∃ r : R, s r = x ∧ P (t r))
    (hslice : ∀ y : U, P y →
      ∃ (V : Scheme.{u}) (g : V ⟶ U), LocallyOfFiniteType g ∧
        Etale (pullback.snd g t ≫ s) ∧ y ∈ Set.range g) :
    EtaleRelationSliceData t s :=
  Classical.choice (by
    obtain ⟨V, g, hfg, he, hsurj⟩ :=
      exists_etale_surjective_slice_of_orbit_slices t s hr P horbit hslice
    exact ⟨⟨V, g, hfg, he, hsurj⟩⟩)

end Langlands.AlgebraicGeometry
