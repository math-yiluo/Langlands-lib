/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import WeilConjectures.AlgebraicGeometry.GenericOpenFibreDensity

/-! # Generic affine chart and geometric fibre density

Source: Stacks Project, Tags 0559 and 054X.
-/

@[expose] public section

universe u
open CategoryTheory Limits Topology
namespace AlgebraicGeometry

/-- An open source subscheme with geometrically irreducible generic fibre has dense
image in every geometric fibre after shrinking the base.

Source: Stacks Project, Tag 054X and the affine-open reduction in Tag 0559.
Proof: the generic fibre of the open subscheme is nonempty by geometric
irreducibility. It is open in the irreducible generic fibre of X, so is dense.
Its closed complement therefore has nowhere dense generic fibre. To prove the shrinking
assertion of Tag 054X, reduce the base,
then use generic
flatness to shrink to an affine base where both X and the reduced closed complement
Z are flat and locally finitely presented. If Z has interior in a fibre, choose a generic
point of an irreducible component of that fibre lying in Z. Flatness of Z lifts
this point by generalization to the generic fibre. Constancy of fibre dimension
along this generalization for the two flat locally finitely presented morphisms (Stacks
Lemma 37.22.10) makes the generic dimension of Z equal that of X at the lifted
point. This contradicts the nowhere dense generic complement. Thus on this
neighbourhood the complement is nowhere dense in every fibre. For any residue-field
extension, the base-change projection is an open surjection, so the inverse image
of the dense open is still dense. The displayed map is the base change of the open
immersion from the open fibre to the full fibre and has exactly this inverse image
as its range. Thus it has dense range, as claimed. Reduction of the base in Tag
054X preserves fibre spaces, so nilpotents do not require extra hypotheses.

(blueprint: lem-sbc-generic-open-geometric-fibre-density) -/
theorem exists_open_geometric_fibre_dense_of_open {X T : Scheme.{u}}
    (f : X ⟶ T) [LocallyOfFiniteType f] [QuasiCompact f]
    (W : X.Opens) (η : T) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (f.fiberToSpecResidueField η))
    (hWgeom : GeometricallyIrreducible ((W.ι ≫ f).fiberToSpecResidueField η)) :
    ∃ U : T.Opens, η ∈ U ∧
      ∀ (t : T), t ∈ U → ∀ (K : Type u) [Field K]
        (z : Spec (.of K) ⟶ Spec (T.residueField t)),
        DenseRange (pullback.map ((W.ι ≫ f).fiberToSpecResidueField t) z
          (f.fiberToSpecResidueField t) z
          (pullback.map (W.ι ≫ f) (T.fromSpecResidueField t) f
            (T.fromSpecResidueField t) W.ι (𝟙 _) (𝟙 _) (by simp) (by simp))
          (𝟙 _) (𝟙 _) (by simp [Scheme.Hom.fiberToSpecResidueField]) (by simp)) := by
  have := hgeom
  have := hWgeom
  have : IrreducibleSpace (f.fiber η) :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton
      (f.fiberToSpecResidueField η)
  have : IrreducibleSpace ((W.ι ≫ f).fiber η) :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton
      ((W.ι ≫ f).fiberToSpecResidueField η)
  let i := pullback.map (W.ι ≫ f) (T.fromSpecResidueField η) f
    (T.fromSpecResidueField η) W.ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have : Nonempty ↥(pullback (W.ι ≫ f) (T.fromSpecResidueField η)) :=
    inferInstanceAs (Nonempty ((W.ι ≫ f).fiber η))
  have : PreirreducibleSpace ↥(pullback f (T.fromSpecResidueField η)) :=
    inferInstanceAs (PreirreducibleSpace (f.fiber η))
  have hi : DenseRange i :=
    i.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace i
  have hrange (t : T) :
      Set.range (pullback.map (W.ι ≫ f) (T.fromSpecResidueField t) f
        (T.fromSpecResidueField t) W.ι (𝟙 _) (𝟙 _) (by simp) (by simp)) =
        (f.fiberι t) ⁻¹' (W : Set X) := by
    rw [Scheme.Pullback.range_map]
    simp [Scheme.Hom.fiberι]
    rfl
  have hdense : Dense ((f.fiberι η) ⁻¹' (W : Set X)) := by
    rw [← hrange η]
    exact hi
  obtain ⟨U, hηU, hU⟩ := exists_open_fibre_dense_of_generic_dense f W η hη hdense
  refine ⟨U, hηU, ?_⟩
  intro t ht K _ z
  rw [denseRange_iff_closure_range]
  rw [Scheme.Pullback.range_map]
  have hid : Set.range (𝟙 (Spec (.of K))) = Set.univ := by
    exact Set.range_eq_univ.mpr (Scheme.Hom.surjective (𝟙 (Spec (.of K))))
  rw [hid, Set.preimage_univ, Set.inter_univ]
  have hd : Dense (Set.range (pullback.map (W.ι ≫ f) (T.fromSpecResidueField t) f
      (T.fromSpecResidueField t) W.ι (𝟙 _) (𝟙 _) (by simp) (by simp))) := by
    rw [hrange t]
    exact hU t ht
  exact (hd.preimage (pullback.fst (f.fiberToSpecResidueField t) z).isOpenMap).closure_eq

end AlgebraicGeometry
