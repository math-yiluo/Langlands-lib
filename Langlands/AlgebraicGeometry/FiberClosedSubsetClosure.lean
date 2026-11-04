import Langlands.AlgebraicGeometry.ClosedSubschemeFiberCover
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Actual closed-subscheme closures of closed subsets of a fibre -/

noncomputable section

universe u v

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.GenericImagePattern

variable {X Y : Scheme.{u}}

/-- The vanishing ideal of the closure in X of a closed subset of an actual fibre. -/
def fiberClosedSubsetClosureIdeal (f : X ⟶ Y) (y : Y)
    (C : TopologicalSpace.Closeds (f.fiber y)) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨closure ((f.fiberι y) '' (C : Set (f.fiber y))), isClosed_closure⟩

/-- The actual closed subscheme of X associated to the closure of the fibre subset. -/
abbrev fiberClosedSubsetClosure (f : X ⟶ Y) (y : Y)
    (C : TopologicalSpace.Closeds (f.fiber y)) : Scheme.{u} :=
  (fiberClosedSubsetClosureIdeal f y C).subscheme

/-- Its actual closed immersion into X. -/
abbrev fiberClosedSubsetClosureι (f : X ⟶ Y) (y : Y)
    (C : TopologicalSpace.Closeds (f.fiber y)) : fiberClosedSubsetClosure f y C ⟶ X :=
  (fiberClosedSubsetClosureIdeal f y C).subschemeι

/-- The underlying range is precisely the closure of the original fibre subset's image. -/
theorem range_fiberClosedSubsetClosureι (f : X ⟶ Y) (y : Y)
    (C : TopologicalSpace.Closeds (f.fiber y)) :
    Set.range (fiberClosedSubsetClosureι f y C) =
      closure ((f.fiberι y) '' (C : Set (f.fiber y))) := by
  rw [fiberClosedSubsetClosureι, Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- Restricting the closure back to the original fibre recovers the closed subset exactly. -/
theorem preimage_range_fiberClosedSubsetClosureι (f : X ⟶ Y) (y : Y)
    (C : TopologicalSpace.Closeds (f.fiber y)) :
    (f.fiberι y) ⁻¹' Set.range (fiberClosedSubsetClosureι f y C) = C := by
  rw [range_fiberClosedSubsetClosureι,
    ← (f.fiberι y).isEmbedding.closure_eq_preimage_closure_image, C.isClosed.closure_eq]

/-- For a whole family, the original-fibre construction recovers each original subset. -/
theorem fiberSubschemeSets_fiberClosedSubsetClosures {ι : Type v}
    (f : X ⟶ Y) (y : Y) (C : ι → TopologicalSpace.Closeds (f.fiber y)) (i : ι) :
    fiberSubschemeSets f (fun j => fiberClosedSubsetClosureι f y (C j)) y i = C i :=
  preimage_range_fiberClosedSubsetClosureι f y (C i)

/-- The actual base-changed range on the original fibre is the original closed subset. -/
theorem range_baseChange_fiberClosedSubsetClosureι (f : X ⟶ Y) (y : Y)
    (C : TopologicalSpace.Closeds (f.fiber y)) :
    Set.range (pullback.snd (fiberClosedSubsetClosureι f y C) (f.fiberι y)) = C := by
  rw [Scheme.Pullback.range_snd, preimage_range_fiberClosedSubsetClosureι]

/-- Original coverage is exactly coverage of the fibre by these actual closed subschemes. -/
theorem closedSubschemeFiberCover_fiberClosedSubsetClosures_iff {ι : Type v}
    (f : X ⟶ Y) (y : Y) (C : ι → TopologicalSpace.Closeds (f.fiber y)) :
    closedSubschemeFiberCover f (fun i => fiberClosedSubsetClosureι f y (C i)) y ↔
      (⋃ i, (C i : Set (f.fiber y))) = Set.univ := by
  simp only [closedSubschemeFiberCover, fiberSubschemeSets_fiberClosedSubsetClosures]

/-- Original incidence is exactly incidence of the closed-subscheme family in that fibre. -/
theorem closedSubschemeFiberIncidence_fiberClosedSubsetClosures_iff {ι : Type v}
    (f : X ⟶ Y) (y : Y) (C : ι → TopologicalSpace.Closeds (f.fiber y)) (i j : ι) :
    closedSubschemeFiberIncidence f (fun k => fiberClosedSubsetClosureι f y (C k)) y i j ↔
      ((C i : Set (f.fiber y)) ∩ C j).Nonempty := by
  simp only [closedSubschemeFiberIncidence, fiberSubschemeSets_fiberClosedSubsetClosures]

/-- A finite closed cover of the generic fibre has actual closures covering all nearby
 fibres, with exactly the original pairwise nonempty-intersection pattern. -/
theorem exists_open_fiberClosedSubsetClosures_cover_and_incidence
    {ι : Type v} [Finite ι] [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    {η : Y} (hη : IsGenericPoint η (Set.univ : Set Y))
    (C : ι → TopologicalSpace.Closeds (f.fiber η))
    (hcover : (⋃ i, (C i : Set (f.fiber η))) = Set.univ) :
    ∃ U : Set Y, IsOpen U ∧ η ∈ U ∧ ∀ y ∈ U,
      closedSubschemeFiberCover f (fun i => fiberClosedSubsetClosureι f η (C i)) y ∧
      ∀ i j,
        closedSubschemeFiberIncidence f (fun k => fiberClosedSubsetClosureι f η (C k)) y i j ↔
          ((C i : Set (f.fiber η)) ∩ C j).Nonempty := by
  obtain ⟨U, hU, hηU, hpattern⟩ :=
    exists_open_closedSubschemeFiberCover_and_incidence f
      (fun i => fiberClosedSubsetClosureι f η (C i)) hη
  refine ⟨U, hU, hηU, fun y hy => ⟨?_, ?_⟩⟩
  · exact (hpattern y hy).1.mpr
      ((closedSubschemeFiberCover_fiberClosedSubsetClosures_iff f η C).mpr hcover)
  · intro i j
    exact ((hpattern y hy).2 i j).trans
      (closedSubschemeFiberIncidence_fiberClosedSubsetClosures_iff f η C i j)

/-- An actual maximal irreducible component of an actual fibre as a closed subset. -/
def fiberComponentClosedSubset (f : X ⟶ Y) (y : Y)
    (C : irreducibleComponents (f.fiber y)) : TopologicalSpace.Closeds (f.fiber y) :=
  ⟨C.val, isClosed_of_mem_irreducibleComponents C.val C.property⟩

/-- The actual closure immersion for a maximal irreducible component of the fibre. -/
abbrev fiberComponentClosureι (f : X ⟶ Y) (y : Y)
    (C : irreducibleComponents (f.fiber y)) :
    fiberClosedSubsetClosure f y (fiberComponentClosedSubset f y C) ⟶ X :=
  fiberClosedSubsetClosureι f y (fiberComponentClosedSubset f y C)

/-- The actual generic irreducible components have finite closed-subscheme closures
 covering every nearby fibre with the exact generic incidence pattern. -/
theorem exists_open_fiberComponentClosures_cover_and_incidence
    [IsNoetherian Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    {η : Y} (hη : IsGenericPoint η (Set.univ : Set Y)) :
    ∃ U : Set Y, IsOpen U ∧ η ∈ U ∧ ∀ y ∈ U,
      closedSubschemeFiberCover f (fiberComponentClosureι f η) y ∧
      ∀ C D : irreducibleComponents (f.fiber η),
        closedSubschemeFiberIncidence f (fiberComponentClosureι f η) y C D ↔
          (C.val ∩ D.val).Nonempty := by
  let : LocallyOfFiniteType (f.fiberToSpecResidueField η) := by
    change LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField η))
    infer_instance
  let : IsNoetherian (f.fiber η) :=
    { toIsLocallyNoetherian :=
        LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField η)
      toCompactSpace := inferInstance }
  let := (NoetherianSpace.finite_irreducibleComponents (α := f.fiber η)).to_subtype
  apply exists_open_fiberClosedSubsetClosures_cover_and_incidence f hη
    (fiberComponentClosedSubset f η)
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr
    ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩,
      mem_irreducibleComponent⟩

end Langlands.AlgebraicGeometry.GenericImagePattern
