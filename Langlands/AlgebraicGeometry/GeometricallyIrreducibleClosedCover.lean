import Langlands.AlgebraicGeometry.SchemeComponentGeometry

/-! # Components of finite geometrically irreducible closed covers -/

noncomputable section

universe u v

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

variable {X : Scheme.{u}} {ι : Type v} [Finite ι]
variable {Z : ι → Scheme.{u}} (i : ∀ a, Z a ⟶ X)

/-- Every maximal component of a finite irreducible closed cover is a member of the cover. -/
theorem exists_range_eq_component_of_finite_closed_cover
    [∀ a, IsClosedImmersion (i a)] [∀ a, IrreducibleSpace (Z a)]
    (hcover : (⋃ a, Set.range (i a)) = Set.univ)
    (C : irreducibleComponents X) :
    ∃ a, Set.range (i a) = C.val := by
  classical
  let _ := Fintype.ofFinite ι
  let s : Finset (Set X) := Finset.univ.image fun a ↦ Set.range (i a)
  have hs : ∀ t ∈ s, IsClosed t := by
    intro t ht
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp ht
    exact (i a).isClosedEmbedding.isClosed_range
  have hCs : C.val ⊆ ⋃₀ (s : Set (Set X)) := by
    intro x hx
    have hxcover : x ∈ ⋃ a, Set.range (i a) := by rw [hcover]; trivial
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hxcover
    exact Set.mem_sUnion.mpr
      ⟨Set.range (i a), Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩, ha⟩
  obtain ⟨t, ht, hCt⟩ := isIrreducible_iff_sUnion_isClosed.mp C.property.1 s hs hCs
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp ht
  have ha : IsIrreducible (Set.range (i a)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (Z a)).image (i a) (i a).continuous.continuousOn
  exact ⟨a, (C.property.2 ha hCt).antisymm hCt⟩

/-- Choose an actual member of a finite closed cover that equals each maximal component. -/
def componentClosedCoverIndex
    [∀ a, IsClosedImmersion (i a)] [∀ a, IrreducibleSpace (Z a)]
    (hcover : (⋃ a, Set.range (i a)) = Set.univ)
    (C : irreducibleComponents X) : ι :=
  Classical.choose (exists_range_eq_component_of_finite_closed_cover i hcover C)

theorem range_componentClosedCoverIndex
    [∀ a, IsClosedImmersion (i a)] [∀ a, IrreducibleSpace (Z a)]
    (hcover : (⋃ a, Set.range (i a)) = Set.univ)
    (C : irreducibleComponents X) :
    Set.range (i (componentClosedCoverIndex i hcover C)) = C.val :=
  Classical.choose_spec (exists_range_eq_component_of_finite_closed_cover i hcover C)

/-- A finite geometrically irreducible closed cover over a field makes all actual
maximal components geometrically irreducible with their reduced closed structures. -/
theorem componentsGeometricallyIrreducible_of_finite_closed_cover
    {K : Type u} [Field K] (f : X ⟶ Spec (CommRingCat.of K))
    [∀ a, IsClosedImmersion (i a)]
    (hgi : ∀ a, GeometricallyIrreducible (i a ≫ f))
    (hcover : (⋃ a, Set.range (i a)) = Set.univ) :
    ComponentsGeometricallyIrreducible f := by
  letI : ∀ a, IrreducibleSpace (Z a) := fun a ↦ by
    letI := hgi a
    exact GeometricallyIrreducible.irreducibleSpace_of_subsingleton (i a ≫ f)
  intro C
  obtain ⟨a, ha⟩ := exists_range_eq_component_of_finite_closed_cover i hcover C
  let j := (Scheme.IdealSheafData.vanishingIdeal
    (⟨C.val, isClosed_of_mem_irreducibleComponents C.val C.property⟩ :
      TopologicalSpace.Closeds X)).subschemeι
  have hj : Set.range (i a) = Set.range j := by
    rw [ha, Scheme.IdealSheafData.range_subschemeι]
    rfl
  exact (GenericImagePattern.geometricallyIrreducible_iff_of_closedImmersion_range_eq
    f (i a) j hj).mp (hgi a)

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
