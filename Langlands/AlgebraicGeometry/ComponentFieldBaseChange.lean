import Langlands.AlgebraicGeometry.GeometricallyIrreducibleClosedCover

/-! # Actual components under further field base change -/

noncomputable section

universe u

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

variable {X S T : Scheme.{u}}

/-- The actual base change of the reduced closed inclusion of a maximal component. -/
def componentBaseChangeInclusion (f : X ⟶ S) (e : T ⟶ S)
    (C : irreducibleComponents X) :
    pullback
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨C.val, isClosed_of_mem_irreducibleComponents C.val C.property⟩ :
            TopologicalSpace.Closeds X)).subschemeι
        (pullback.fst f e) ⟶ pullback f e :=
  pullback.snd _ _

instance (f : X ⟶ S) (e : T ⟶ S) (C : irreducibleComponents X) :
    IsClosedImmersion (componentBaseChangeInclusion f e C) := by
  unfold componentBaseChangeInclusion
  infer_instance

/-- The support of the pulled-back component is the inverse image of its support. -/
theorem range_componentBaseChangeInclusion (f : X ⟶ S) (e : T ⟶ S)
    (C : irreducibleComponents X) :
    Set.range (componentBaseChangeInclusion f e C) = (pullback.fst f e) ⁻¹' C.val := by
  rw [componentBaseChangeInclusion, Scheme.Pullback.range_snd,
    Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- The actual pulled-back components form a closed cover after arbitrary base change. -/
theorem iUnion_range_componentBaseChangeInclusion (f : X ⟶ S) (e : T ⟶ S) :
    (⋃ C : irreducibleComponents X, Set.range (componentBaseChangeInclusion f e C)) =
      Set.univ := by
  simp_rw [range_componentBaseChangeInclusion, ← Set.preimage_iUnion]
  rw [Set.iUnion_coe_set, ← Set.sUnion_eq_biUnion, sUnion_irreducibleComponents,
    Set.preimage_univ]

/-- Geometric irreducibility of a reduced component persists on its actual base change.
The base-changed closed scheme itself need not be reduced. -/
theorem geometricallyIrreducible_componentBaseChangeInclusion
    {f : X ⟶ S} (h : ComponentsGeometricallyIrreducible f)
    (e : T ⟶ S) (C : irreducibleComponents X) :
    GeometricallyIrreducible (componentBaseChangeInclusion f e C ≫ pullback.snd f e) := by
  let i := (Scheme.IdealSheafData.vanishingIdeal
    (⟨C.val, isClosed_of_mem_irreducibleComponents C.val C.property⟩ :
      TopologicalSpace.Closeds X)).subschemeι
  have : GeometricallyIrreducible (i ≫ f) := h C
  change GeometricallyIrreducible
    (pullback.snd i (pullback.fst f e) ≫ pullback.snd f e)
  rw [← pullbackRightPullbackFstIso_hom_snd, geometricallyIrreducible_iff]
  rw [MorphismProperty.cancel_left_of_respectsIso
    (geometrically (fun A : Scheme.{u} => IrreducibleSpace A))
    (pullbackRightPullbackFstIso f e i).hom]
  have hgi : GeometricallyIrreducible (pullback.snd (i ≫ f) e) := inferInstance
  exact hgi.geometrically_irreducibleSpace

/-- For a scheme with finitely many maximal components, geometric irreducibility
of its actual reduced components persists after any field-valued base change. -/
theorem ComponentsGeometricallyIrreducible.baseChange
    {f : X ⟶ S} (h : ComponentsGeometricallyIrreducible f)
    [Finite (irreducibleComponents X)] {L : Type u} [Field L]
    (e : Spec (CommRingCat.of L) ⟶ S) :
    ComponentsGeometricallyIrreducible (pullback.snd f e) :=
  componentsGeometricallyIrreducible_of_finite_closed_cover
    (componentBaseChangeInclusion f e) (pullback.snd f e)
    (geometricallyIrreducible_componentBaseChangeInclusion h e)
    (iUnion_range_componentBaseChangeInclusion f e)

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
