import Langlands.AlgebraicGeometry.FiberClosedSubsetClosure
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible

/-! # Geometric properties of actual closed subschemes with equal support -/

noncomputable section

universe u

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.GenericImagePattern

variable {X Z W T S : Scheme.{u}}

/-- Closed immersions with equal underlying ranges have homeomorphic source spaces. -/
def closedImmersionHomeomorphOfRangeEq (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (h : Set.range i = Set.range j) :
    Z ≃ₜ W :=
  i.isEmbedding.toHomeomorph |>.trans
    ((Homeomorph.setCongr h).trans j.isEmbedding.toHomeomorph.symm)

/-- The homeomorphism identifies the two maps to the ambient point space. -/
@[simp]
theorem closedImmersionHomeomorphOfRangeEq_apply (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (h : Set.range i = Set.range j) (z : Z) :
    j (closedImmersionHomeomorphOfRangeEq i j h z) = i z := by
  have he := j.isEmbedding.toHomeomorph.apply_symm_apply
    ((Homeomorph.setCongr h) (i.isEmbedding.toHomeomorph z))
  exact congrArg Subtype.val he

/-- Equal closed supports stay equal after every actual scheme base change. -/
theorem range_baseChange_closedImmersion_eq (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (h : Set.range i = Set.range j)
    (p : T ⟶ X) :
    Set.range (pullback.snd i p) = Set.range (pullback.snd j p) := by
  rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, h]

/-- The underlying spaces of the actual pullbacks are homeomorphic for every base change. -/
def baseChangeClosedImmersionHomeomorphOfRangeEq (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (h : Set.range i = Set.range j)
    (p : T ⟶ X) :
    (pullback i p : Scheme.{u}) ≃ₜ (pullback j p : Scheme.{u}) :=
  closedImmersionHomeomorphOfRangeEq (pullback.snd i p) (pullback.snd j p)
    (range_baseChange_closedImmersion_eq i j h p)

/-- Equal closed supports over X give homeomorphic pullbacks over every base S. -/
def compositeBaseChangeHomeomorphOfRangeEq (f : X ⟶ S) (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (h : Set.range i = Set.range j)
    (e : T ⟶ S) :
    (pullback (i ≫ f) e : Scheme.{u}) ≃ₜ (pullback (j ≫ f) e : Scheme.{u}) :=
  (pullbackRightPullbackFstIso f e i).hom.homeomorph.symm |>.trans
    ((baseChangeClosedImmersionHomeomorphOfRangeEq i j h (pullback.fst f e)).trans
      (pullbackRightPullbackFstIso f e j).hom.homeomorph)

/-- Geometric connectedness depends only on the support of a closed subscheme. -/
theorem geometricallyConnected_iff_of_closedImmersion_range_eq
    (f : X ⟶ S) (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (h : Set.range i = Set.range j) :
    GeometricallyConnected (i ≫ f) ↔ GeometricallyConnected (j ≫ f) := by
  simp only [geometricallyConnected_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  constructor
  · intro H K _ e
    exact (compositeBaseChangeHomeomorphOfRangeEq f i j h e).connectedSpace_iff.mp (H K e)
  · intro H K _ e
    exact (compositeBaseChangeHomeomorphOfRangeEq f i j h e).connectedSpace_iff.mpr (H K e)

/-- Geometric irreducibility depends only on the support of a closed subscheme. -/
theorem geometricallyIrreducible_iff_of_closedImmersion_range_eq
    (f : X ⟶ S) (i : Z ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (h : Set.range i = Set.range j) :
    GeometricallyIrreducible (i ≫ f) ↔ GeometricallyIrreducible (j ≫ f) := by
  simp only [geometricallyIrreducible_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  constructor
  · intro H K _ e
    exact (compositeBaseChangeHomeomorphOfRangeEq f i j h e).irreducibleSpace_iff.mp (H K e)
  · intro H K _ e
    exact (compositeBaseChangeHomeomorphOfRangeEq f i j h e).irreducibleSpace_iff.mpr (H K e)

/-- Recover the underlying space of the original closed fibre subset as an actual subscheme. -/
def fiberClosedSubsetClosureHomeomorph (f : X ⟶ S) (y : S)
    (C : TopologicalSpace.Closeds (f.fiber y)) :
    (pullback (fiberClosedSubsetClosureι f y C) (f.fiberι y) : Scheme.{u}) ≃ₜ
      (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
  closedImmersionHomeomorphOfRangeEq
    (pullback.snd (fiberClosedSubsetClosureι f y C) (f.fiberι y))
    (Scheme.IdealSheafData.vanishingIdeal C).subschemeι (by
      rw [range_baseChange_fiberClosedSubsetClosureι, Scheme.IdealSheafData.range_subschemeι]
      rfl)

/-- The actual residue-field fibre of the closure has exactly the original subspace topology. -/
def fiberClosedSubsetClosureFiberHomeomorph (f : X ⟶ S) (y : S)
    (C : TopologicalSpace.Closeds (f.fiber y)) :
    ((fiberClosedSubsetClosureι f y C ≫ f).fiber y) ≃ₜ (C : Set (f.fiber y)) :=
  (pullbackRightPullbackFstIso f (S.fromSpecResidueField y)
    (fiberClosedSubsetClosureι f y C)).hom.homeomorph.symm |>.trans
    ((pullback.snd (fiberClosedSubsetClosureι f y C) (f.fiberι y)).isEmbedding.toHomeomorph
      |>.trans (Homeomorph.setCongr (range_baseChange_fiberClosedSubsetClosureι f y C)))

/-- Connectedness of that actual fibre is connectedness of the original closed subset. -/
theorem connectedSpace_fiberClosedSubsetClosure_iff (f : X ⟶ S) (y : S)
    (C : TopologicalSpace.Closeds (f.fiber y)) :
    ConnectedSpace ((fiberClosedSubsetClosureι f y C ≫ f).fiber y) ↔
      _root_.IsConnected (C : Set (f.fiber y)) :=
  (fiberClosedSubsetClosureFiberHomeomorph f y C).connectedSpace_iff.trans
    isConnected_iff_connectedSpace.symm

/-- Irreducibility of that actual fibre is irreducibility of the original closed subset. -/
theorem irreducibleSpace_fiberClosedSubsetClosure_iff (f : X ⟶ S) (y : S)
    (C : TopologicalSpace.Closeds (f.fiber y)) :
    IrreducibleSpace ((fiberClosedSubsetClosureι f y C ≫ f).fiber y) ↔
      IsIrreducible (C : Set (f.fiber y)) :=
  (fiberClosedSubsetClosureFiberHomeomorph f y C).irreducibleSpace_iff.trans
    isIrreducible_iff_irreducibleSpace.symm

/-- The original fibre of an actual component closure is irreducible. -/
theorem irreducibleSpace_fiberComponentClosure (f : X ⟶ S) (y : S)
    (C : irreducibleComponents (f.fiber y)) :
    IrreducibleSpace ((fiberComponentClosureι f y C ≫ f).fiber y) :=
  (irreducibleSpace_fiberClosedSubsetClosure_iff f y
    (fiberComponentClosedSubset f y C)).mpr C.property.1

/-- The original closed subscheme and the actual closure fibre have the same geometric
 connectedness over the residue field, even if their scheme structures differ. -/
theorem geometricallyConnected_fiberClosedSubsetClosure_iff (f : X ⟶ S) (y : S)
    (C : TopologicalSpace.Closeds (f.fiber y)) :
    GeometricallyConnected ((fiberClosedSubsetClosureι f y C ≫ f).fiberToSpecResidueField y) ↔
      GeometricallyConnected
        ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ f.fiberToSpecResidueField y) := by
  have h := geometricallyConnected_iff_of_closedImmersion_range_eq
    (f.fiberToSpecResidueField y)
    (pullback.snd (fiberClosedSubsetClosureι f y C) (f.fiberι y))
    (Scheme.IdealSheafData.vanishingIdeal C).subschemeι (by
      rw [range_baseChange_fiberClosedSubsetClosureι, Scheme.IdealSheafData.range_subschemeι]
      rfl)
  refine Iff.trans ?_ h
  change GeometricallyConnected
    (pullback.snd (fiberClosedSubsetClosureι f y C ≫ f) (S.fromSpecResidueField y)) ↔
      GeometricallyConnected
        (pullback.snd (fiberClosedSubsetClosureι f y C)
          (pullback.fst f (S.fromSpecResidueField y)) ≫
            pullback.snd f (S.fromSpecResidueField y))
  rw [← pullbackRightPullbackFstIso_hom_snd]
  simp only [geometricallyConnected_iff]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (geometrically (fun A : Scheme.{u} => ConnectedSpace A))
    (pullbackRightPullbackFstIso f (S.fromSpecResidueField y)
      (fiberClosedSubsetClosureι f y C)).hom _).symm

/-- The original closed subscheme and the actual closure fibre have the same geometric
 irreducibility over the residue field. -/
theorem geometricallyIrreducible_fiberClosedSubsetClosure_iff (f : X ⟶ S) (y : S)
    (C : TopologicalSpace.Closeds (f.fiber y)) :
    GeometricallyIrreducible
      ((fiberClosedSubsetClosureι f y C ≫ f).fiberToSpecResidueField y) ↔
      GeometricallyIrreducible
        ((Scheme.IdealSheafData.vanishingIdeal C).subschemeι ≫ f.fiberToSpecResidueField y) := by
  have h := geometricallyIrreducible_iff_of_closedImmersion_range_eq
    (f.fiberToSpecResidueField y)
    (pullback.snd (fiberClosedSubsetClosureι f y C) (f.fiberι y))
    (Scheme.IdealSheafData.vanishingIdeal C).subschemeι (by
      rw [range_baseChange_fiberClosedSubsetClosureι, Scheme.IdealSheafData.range_subschemeι]
      rfl)
  refine Iff.trans ?_ h
  change GeometricallyIrreducible
    (pullback.snd (fiberClosedSubsetClosureι f y C ≫ f) (S.fromSpecResidueField y)) ↔
      GeometricallyIrreducible
        (pullback.snd (fiberClosedSubsetClosureι f y C)
          (pullback.fst f (S.fromSpecResidueField y)) ≫
            pullback.snd f (S.fromSpecResidueField y))
  rw [← pullbackRightPullbackFstIso_hom_snd]
  simp only [geometricallyIrreducible_iff]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (geometrically (fun A : Scheme.{u} => IrreducibleSpace A))
    (pullbackRightPullbackFstIso f (S.fromSpecResidueField y)
      (fiberClosedSubsetClosureι f y C)).hom _).symm

end Langlands.AlgebraicGeometry.GenericImagePattern
