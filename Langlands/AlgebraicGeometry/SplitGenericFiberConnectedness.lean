import Langlands.AlgebraicGeometry.SplitGenericComponentSpreading
import Langlands.AlgebraicGeometry.GeometricallyConnectedClosedCoverStatement

/-! # Conditional connectedness constancy for split generic fibres -/

noncomputable section

universe u v

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

namespace SchemeFiberGeometry

/-- Geometric connectedness of actual residue-field fibres has the same truth
value as at the given point throughout an open neighbourhood of that point. -/
def GeometricallyConnectedFiberConstancyAt {X Y : Scheme.{u}} (f : X ⟶ Y)
    (η : Y) : Prop :=
  ∃ U : Set Y, IsOpen U ∧ η ∈ U ∧ ∀ y ∈ U,
    GeometricallyConnected (f.fiberToSpecResidueField y) ↔
      GeometricallyConnected (f.fiberToSpecResidueField η)

end SchemeFiberGeometry

namespace GenericImagePattern

open SchemeFiberGeometry ComponentIncidence

variable {X Y : Scheme.{u}}

/-- The field closed-cover criterion applies to the actual pullback closed
immersions covering a residue-field fibre. -/
theorem geometricallyConnected_fiber_iff_intersectionChains
    (hcriterion : FiniteClosedGeometricallyConnectedCoverCriterion.{u, v})
    {ι : Type v} [Finite ι] (f : X ⟶ Y)
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (g i)] (y : Y)
    (hcover : closedSubschemeFiberCover f g y)
    (hpieces : ∀ i, GeometricallyConnected
      (pullback.snd (g i) (f.fiberι y) ≫ f.fiberToSpecResidueField y)) :
    GeometricallyConnected (f.fiberToSpecResidueField y) ↔
      IntersectionChainConnected (fiberSubschemeSets f g y) := by
  have h := hcriterion (Y.residueField y) (f.fiberToSpecResidueField y)
    (fun i => pullback.snd (g i) (f.fiberι y))
    ((closedSubschemeFiberCover_iff_baseChangeRanges f g y).mp hcover) hpieces
  simpa only [range_baseChange_eq_fiberSubschemeSets] using h

/-- Assuming geometric-irreducibility spreading and the field closed-cover
criterion, a finite geometrically irreducible closed generic cover gives
Boolean geometric-connectedness constancy near the generic point. -/
theorem geometricallyConnectedFiberConstancyAt_of_split_closedCover
    (hspread : FiniteTypeGeometricallyIrreducibleGenericSpreading.{u})
    (hcriterion : FiniteClosedGeometricallyConnectedCoverCriterion.{u, v})
    {ι : Type v} [Finite ι] [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    {η : Y} (hη : IsGenericPoint η (Set.univ : Set Y))
    (C : ι → TopologicalSpace.Closeds (f.fiber η))
    (hcover : (⋃ i, (C i : Set (f.fiber η))) = Set.univ)
    (hgeom : ∀ i, GeometricallyIrreducible
      ((Scheme.IdealSheafData.vanishingIdeal (C i)).subschemeι ≫
        f.fiberToSpecResidueField η)) :
    GeometricallyConnectedFiberConstancyAt f η := by
  obtain ⟨U, hU, hηU, hpattern⟩ :=
    exists_open_closureCover_geometricallyIrreducible_and_incidence
      hspread f hη C hcover hgeom
  let g := fun i => fiberClosedSubsetClosureι f η (C i)
  have hfiber (y : Y) (hy : y ∈ U) :
      GeometricallyConnected (f.fiberToSpecResidueField y) ↔
        IntersectionChainConnected (fiberSubschemeSets f g y) := by
    apply geometricallyConnected_fiber_iff_intersectionChains
      hcriterion f g y (hpattern y hy).1
    intro i
    let : GeometricallyIrreducible
        (fiberClosedSubsetClosureFiberMap f η (C i) y ≫
          f.fiberToSpecResidueField y) := (hpattern y hy).2.1 i
    exact geometricallyConnected_of_geometricallyIrreducible _
  refine ⟨U, hU, hηU, ?_⟩
  intro y hy
  apply (hfiber y hy).trans
  apply Iff.trans _ (hfiber η hηU).symm
  apply intersectionChainConnected_congr
    (fiberSubschemeSets f g y) (fiberSubschemeSets f g η) (Equiv.refl ι)
  intro i j
  exact ((hpattern y hy).2.2 i j).trans ((hpattern η hηU).2.2 i j).symm

/-- Specialization to all actual maximal irreducible generic-fibre components,
provided those components are geometrically irreducible. -/
theorem geometricallyConnectedFiberConstancyAt_of_split_components
    (hspread : FiniteTypeGeometricallyIrreducibleGenericSpreading.{u})
    (hcriterion : FiniteClosedGeometricallyConnectedCoverCriterion.{u, u})
    [IsNoetherian Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    {η : Y} (hη : IsGenericPoint η (Set.univ : Set Y))
    (hgeom : FiberComponentsGeometricallyIrreducible f η) :
    GeometricallyConnectedFiberConstancyAt f η := by
  let : LocallyOfFiniteType (f.fiberToSpecResidueField η) := by
    change LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField η))
    infer_instance
  let : IsNoetherian (f.fiber η) :=
    { toIsLocallyNoetherian :=
        LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField η)
      toCompactSpace := inferInstance }
  let := (NoetherianSpace.finite_irreducibleComponents (α := f.fiber η)).to_subtype
  exact geometricallyConnectedFiberConstancyAt_of_split_closedCover
    hspread hcriterion f hη (fiberComponentClosedSubset f η)
    (iUnion_componentSets (f.fiber η)) hgeom

end GenericImagePattern

end Langlands.AlgebraicGeometry
