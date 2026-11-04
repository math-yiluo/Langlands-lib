import Langlands.AlgebraicGeometry.ClosedSubschemeSupportGeometry
import Langlands.AlgebraicGeometry.IrreducibleComponentIncidence
import Langlands.AlgebraicGeometry.GeometricallyIrreducibleGenericSpreadingStatement
import Langlands.AlgebraicGeometry.FiniteEtaleGenericComponentSplittingStatement

/-! # Conditional spreading of actual split generic components -/

noncomputable section

universe u v

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.GenericImagePattern

open SchemeFiberGeometry ComponentIncidence

variable {X Y : Scheme.{u}}

/-- The actual closed immersion of a closure piece into a residue-field fibre. -/
abbrev fiberClosedSubsetClosureFiberMap (f : X ⟶ Y) (η : Y)
    (C : TopologicalSpace.Closeds (f.fiber η)) (y : Y) :
    pullback (fiberClosedSubsetClosureι f η C) (f.fiberι y) ⟶ f.fiber y :=
  pullback.snd _ _

/-- Geometric irreducibility reflects across a cartesian change of base by an
 isomorphism. -/
theorem geometricallyIrreducible_of_isPullback_of_isIso
    {P Z S T : Scheme.{u}} {a : P ⟶ Z} {b : P ⟶ S}
    {c : Z ⟶ T} {d : S ⟶ T} (h : IsPullback a b c d)
    [IsIso d] [GeometricallyIrreducible b] : GeometricallyIrreducible c := by
  have : IsIso a := h.isIso_fst_of_isIso
  have H : geometrically (fun A : Scheme.{u} => IrreducibleSpace A) b :=
    GeometricallyIrreducible.geometrically_irreducibleSpace
  have H' := (MorphismProperty.cancel_right_of_respectsIso
    (geometrically (fun A : Scheme.{u} => IrreducibleSpace A)) b d).mpr H
  have H'' : geometrically (fun A : Scheme.{u} => IrreducibleSpace A) (a ≫ c) :=
    h.w.symm ▸ H'
  exact ⟨(MorphismProperty.cancel_left_of_respectsIso
    (geometrically (fun A : Scheme.{u} => IrreducibleSpace A)) a c).mp H''⟩

set_option backward.isDefEq.respectTransparency false in
/-- Geometric irreducibility on an open restriction gives the property of each
 original residue-field fibre at a point of that open. -/
theorem geometricallyIrreducible_fiber_of_restrict (f : X ⟶ Y)
    (V : Y.Opens) [GeometricallyIrreducible (f ∣_ V)] (y : Y) (hy : y ∈ V) :
    GeometricallyIrreducible (f.fiberToSpecResidueField y) := by
  let y' : V.toScheme := ⟨y, hy⟩
  have : IsIso (V.ι.residueFieldMap y') := inferInstance
  have : IsIso (Spec.map (V.ι.residueFieldMap y')) := inferInstance
  have h := isPullback_fiberToSpecResidueField_of_isPullback
    (isPullback_morphismRestrict f V).flip y'
  exact geometricallyIrreducible_of_isPullback_of_isIso h

/-- The map of the actual closure piece over a fibre is geometrically
 irreducible exactly when the actual fibre of the closure morphism is. -/
theorem geometricallyIrreducible_closureFiberι_iff (f : X ⟶ Y) (η : Y)
    (C : TopologicalSpace.Closeds (f.fiber η)) (y : Y) :
    GeometricallyIrreducible
      (fiberClosedSubsetClosureFiberMap f η C y ≫ f.fiberToSpecResidueField y) ↔
    GeometricallyIrreducible
      ((fiberClosedSubsetClosureι f η C ≫ f).fiberToSpecResidueField y) := by
  change GeometricallyIrreducible
      (pullback.snd (fiberClosedSubsetClosureι f η C)
        (pullback.fst f (Y.fromSpecResidueField y)) ≫
          pullback.snd f (Y.fromSpecResidueField y)) ↔
    GeometricallyIrreducible
      (pullback.snd (fiberClosedSubsetClosureι f η C ≫ f) (Y.fromSpecResidueField y))
  rw [← pullbackRightPullbackFstIso_hom_snd]
  simp only [geometricallyIrreducible_iff]
  exact MorphismProperty.cancel_left_of_respectsIso
    (geometrically (fun A : Scheme.{u} => IrreducibleSpace A))
    (pullbackRightPullbackFstIso f (Y.fromSpecResidueField y)
      (fiberClosedSubsetClosureι f η C)).hom _

/-- Geometric irreducibility includes geometric connectedness. -/
theorem geometricallyConnected_of_geometricallyIrreducible
    {Z S : Scheme.{u}} (g : Z ⟶ S) [GeometricallyIrreducible g] :
    GeometricallyConnected g := by
  constructor
  intro K _ e T fst snd h
  let : IrreducibleSpace T :=
    GeometricallyIrreducible.geometrically_irreducibleSpace e fst snd h
  infer_instance

/-- Assuming the full geometric-irreducibility spreading statement, a finite
 geometrically irreducible closed cover of a generic fibre extends to actual
 nearby closed covers with the same incidence pattern and geometric properties. -/
theorem exists_open_closureCover_geometricallyIrreducible_and_incidence
    (hspread : FiniteTypeGeometricallyIrreducibleGenericSpreading.{u})
    {ι : Type v} [Finite ι] [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    {η : Y} (hη : IsGenericPoint η (Set.univ : Set Y))
    (C : ι → TopologicalSpace.Closeds (f.fiber η))
    (hcover : (⋃ i, (C i : Set (f.fiber η))) = Set.univ)
    (hgeom : ∀ i, GeometricallyIrreducible
      ((Scheme.IdealSheafData.vanishingIdeal (C i)).subschemeι ≫
        f.fiberToSpecResidueField η)) :
    ∃ U : Set Y, IsOpen U ∧ η ∈ U ∧ ∀ y ∈ U,
      closedSubschemeFiberCover f (fun i => fiberClosedSubsetClosureι f η (C i)) y ∧
      (∀ i, GeometricallyIrreducible
        (fiberClosedSubsetClosureFiberMap f η (C i) y ≫ f.fiberToSpecResidueField y)) ∧
      ∀ i j,
        closedSubschemeFiberIncidence f (fun k => fiberClosedSubsetClosureι f η (C k)) y i j ↔
          ((C i : Set (f.fiber η)) ∩ C j).Nonempty := by
  classical
  have hpiece (i : ι) :
      ∃ V : Y.Opens, η ∈ V ∧
        GeometricallyIrreducible ((fiberClosedSubsetClosureι f η (C i) ≫ f) ∣_ V) := by
    apply hspread (fiberClosedSubsetClosureι f η (C i) ≫ f) η hη
    exact (geometricallyIrreducible_fiberClosedSubsetClosure_iff f η (C i)).mpr (hgeom i)
  choose V hηV hV using hpiece
  obtain ⟨W, hW, hηW, hpattern⟩ :=
    exists_open_fiberClosedSubsetClosures_cover_and_incidence f hη C hcover
  refine ⟨W ∩ ⋂ i, (V i : Set Y),
    hW.inter (isOpen_iInter_of_finite fun i => (V i).isOpen),
    ⟨hηW, Set.mem_iInter.mpr hηV⟩, ?_⟩
  intro y hy
  refine ⟨(hpattern y hy.1).1, ?_, (hpattern y hy.1).2⟩
  intro i
  let : GeometricallyIrreducible
      ((fiberClosedSubsetClosureι f η (C i) ≫ f) ∣_ V i) := hV i
  exact (geometricallyIrreducible_closureFiberι_iff f η (C i) y).mpr
    (geometricallyIrreducible_fiber_of_restrict
      (fiberClosedSubsetClosureι f η (C i) ≫ f) (V i) y (Set.mem_iInter.mp hy.2 i))

/-- The finite-cover construction applies to all actual generic-fibre components
 when their reduced induced schemes are geometrically irreducible. -/
theorem exists_open_genericComponentClosures_geometricallyIrreducible_and_incidence
    (hspread : FiniteTypeGeometricallyIrreducibleGenericSpreading.{u})
    [IsNoetherian Y] (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    {η : Y} (hη : IsGenericPoint η (Set.univ : Set Y))
    (hgeom : FiberComponentsGeometricallyIrreducible f η) :
    ∃ U : Set Y, IsOpen U ∧ η ∈ U ∧ ∀ y ∈ U,
      closedSubschemeFiberCover f (fiberComponentClosureι f η) y ∧
      (∀ C, GeometricallyIrreducible
        (pullback.snd (fiberComponentClosureι f η C) (f.fiberι y) ≫
          f.fiberToSpecResidueField y)) ∧
      ∀ C D,
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
  exact exists_open_closureCover_geometricallyIrreducible_and_incidence
    hspread f hη (fiberComponentClosedSubset f η) (iUnion_componentSets (f.fiber η)) hgeom

end Langlands.AlgebraicGeometry.GenericImagePattern
