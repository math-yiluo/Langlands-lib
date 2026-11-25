/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.RingTheory.Depth
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.EquidimensionalFibreOpenPartition
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension

/-! # Relative dimension decomposition of a fibre Cohen-Macaulay open

Source: Stacks Project, Tags 02NM, 02NJ and 0A21.
(blueprint: lem-sbc-cohen-macaulay-fibre-dimension-decomposition)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A fibre Cohen-Macaulay open partitions into open pieces of constant local fibre dimension.

Source: Stacks Project, Tag 02NM, using the equidimensional convention of Tag 02NJ
and local dimension of locally algebraic schemes (Tag 0A21 (3), (5)).
Proof: Restrict f over U and then restrict its source to W. Flatness and local finite
presentation survive both restrictions. The fibres are locally Noetherian. Each of
their stalks is a stalk of an original fibre, via the open restriction inclusions and
the residue-field isomorphisms. The hypothesis on depth therefore says all these
fibres are Cohen-Macaulay. Tag 02NM gives a coproduct decomposition of W into clopen
subschemes indexed by the nonnegative integer relative dimension. By Tag 02NJ each
nonempty fibre of the nth piece is equidimensional of dimension n. At each point,
shrink any open neighbourhood to a finite-type affine neighbourhood. Every component
through that point has dimension n; its nonempty open subsets still have dimension n
by Tag 0A21. Consequently the infimum of neighbourhood dimensions is n. The fibre
inclusion into the original fibre is an open immersion. The already proved
`IsOpen.topologicalKrullDimAt_eq` preserves local topological dimension on its image.
Map each piece into X: its image V n is open, the images are pairwise disjoint,
and their union is W. Empty pieces and empty W cause no exception.
(blueprint: lem-sbc-cohen-macaulay-fibre-dimension-decomposition) -/
theorem exists_fibre_dimension_open_partition_of_depth_eq_ringKrullDim
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)] (W : X.Opens)
    (hW : ∀ y ∈ W, f y ∈ U ∧
      (IsLocalRing.depth (R := (f.fiber (f y)).presheaf.stalk (f.asFiber y))
        ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber (f y)).presheaf.stalk (f.asFiber y))) :
    ∃ V : ℕ → X.Opens, (⨆ n, V n) = W ∧
      Pairwise (fun m n => Disjoint (V m) (V n)) ∧
      ∀ n y, y ∈ V n → topologicalKrullDimAt (f.asFiber y) = (n : WithBot ℕ∞) := by
  obtain ⟨V, hcover, hdisj, hdim⟩ :=
    exists_equidimensional_fibre_open_partition_of_depth_eq_ringKrullDim f U W hW
  refine ⟨V, hcover, hdisj, ?_⟩
  intro n y hy
  have hyW : y ∈ W := hcover ▸ (le_iSup V n) hy
  let tU : U := ⟨f y, (hW y hyW).1⟩
  let q := CategoryTheory.Limits.pullback.map (f ∣_ U)
    (U.toScheme.fromSpecResidueField tU) f
    (T.fromSpecResidueField (U.ι tU)) (f ⁻¹ᵁ U).ι
    (Spec.map (U.ι.residueFieldMap tU)) U.ι (by simp)
    (by exact (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField U.ι tU).symm)
  have hsq := isPullback_fiberToSpecResidueField_of_isPullback
    (isPullback_morphismRestrict f U).flip tU
  have : IsIso q := hsq.isIso_fst_of_isIso
  have : LocallyOfFiniteType ((f ∣_ U).fiberToSpecResidueField tU) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have heq : f.fiberToSpecResidueField (f y) =
      inv q ≫ (f ∣_ U).fiberToSpecResidueField tU ≫
        Spec.map (U.ι.residueFieldMap tU) := by
    rw [← hsq.w, IsIso.inv_hom_id_assoc]
    rfl
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f y)) := by
    rw [heq]
    infer_instance
  exact topologicalKrullDimAt_eq_of_equidimensional_open
    (f.fiberToSpecResidueField (f y)) ((f.fiberι (f y)) ⁻¹ᵁ V n) n
    (hdim n (f y)) (f.asFiber y) (by simpa using hy)

end AlgebraicGeometry
