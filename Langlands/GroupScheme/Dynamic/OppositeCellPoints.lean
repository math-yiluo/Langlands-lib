import Langlands.GroupScheme.QuotientCell
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Absolute.OppositeCellProof

/-! # Points of the opposite cell in a dynamic parabolic quotient

Let `G` be a smooth affine group over a field `k` with a cocharacter `χ`, and `q : G ⟶ Q` a
flat surjective quasi-compact map whose fibers are the right cosets of `P_G(χ)`. The opposite
unipotent subgroup `U_G(χ⁻¹)` maps by an open immersion onto an open `cell χ q` of `Q`. Every
point of `Q` landing in the cell is the image of a unique point of `U_G(χ⁻¹)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic.OppositeCell

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsAffine G.X.left]
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) {Q : Over (Spec (CommRingCat.of k))}
  (q : G.X ⟶ Q)

/-- The opposite cocharacter `t ↦ χ(t⁻¹)`. -/
abbrev opposite : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G :=
  CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ

/-- The inclusion of the opposite unipotent subgroup. -/
abbrev cellMap : (Affine.unipotentScheme (opposite χ)).X ⟶ G.X :=
  (Affine.unipotentHom (opposite χ)).hom.hom

theorem isOpenImmersion_multiplication :
    IsOpenImmersion (QuotientCell.multiplication (Affine.parabolicHom χ) (cellMap χ)).left :=
  oppositeCellStatement k G χ _ _ _ _ (Affine.isRepresentedBy_unipotentHom _)
    (Affine.isRepresentedBy_parabolicHom χ)

variable (hf : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (Dynamic.parabolic χ).carrier T)
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left]

include hf

/-- The opposite unipotent subgroup maps to `Q` by an open immersion. -/
theorem isOpenImmersion_cell : IsOpenImmersion (cellMap χ ≫ q).left := by
  have hP := Affine.isRepresentedBy_parabolicHom χ
  have : Mono (Affine.parabolicHom χ).hom.hom := hP.1
  have := isOpenImmersion_multiplication χ
  exact QuotientCell.isOpenImmersion (Affine.parabolicHom χ) _ q (by rw [hP.2]; exact hf)

omit hf [Flat q.left] [Surjective q.left] [QuasiCompact q.left] in
/-- The opposite cell: the image of `U_G(χ⁻¹)` in `Q` (an open, by `isOpenImmersion_cell`). -/
abbrev cell : Set Q.left :=
  Set.range (cellMap χ ≫ q).left

/-- A point of `Q` landing in the cell is the image of a point of `U_G(χ⁻¹)`. -/
theorem exists_mem_unipotent {T : Over (Spec (CommRingCat.of k))} (y : T ⟶ Q)
    (hy : Set.range y.left ⊆ cell χ q) :
    ∃ u : T ⟶ G.X, u ∈ (Dynamic.unipotent (opposite χ)).carrier T ∧ u ≫ q = y := by
  have := isOpenImmersion_cell χ q hf
  let l := IsOpenImmersion.lift (cellMap χ ≫ q).left y.left hy
  have hl : l ≫ (cellMap χ ≫ q).left = y.left := IsOpenImmersion.lift_fac _ _ _
  let a : T ⟶ (Affine.unipotentScheme (opposite χ)).X := Over.homMk l (by
    have h1 := Over.w (cellMap χ ≫ q)
    have h2 := Over.w y
    rw [← h1, ← Category.assoc, hl, h2])
  refine ⟨a ≫ cellMap χ, ?_, ?_⟩
  · rw [← (Affine.isRepresentedBy_unipotentHom (opposite χ)).2]
    exact ⟨a, rfl⟩
  · apply Over.OverMorphism.ext
    change l ≫ (cellMap χ).left ≫ q.left = y.left
    rw [← hl]
    rfl

/-- Two points of `U_G(χ⁻¹)` with the same image in `Q` are equal. -/
theorem eq_of_mem_unipotent {T : Over (Spec (CommRingCat.of k))} {u u' : T ⟶ G.X}
    (hu : u ∈ (Dynamic.unipotent (opposite χ)).carrier T)
    (hu' : u' ∈ (Dynamic.unipotent (opposite χ)).carrier T) (h : u ≫ q = u' ≫ q) :
    u = u' := by
  have := isOpenImmersion_cell χ q hf
  rw [← (Affine.isRepresentedBy_unipotentHom (opposite χ)).2] at hu hu'
  obtain ⟨a, rfl⟩ := SubgroupFunctor.mem_range.1 hu
  obtain ⟨a', rfl⟩ := SubgroupFunctor.mem_range.1 hu'
  have ha : a = a' := by
    apply Over.OverMorphism.ext
    apply (cancel_mono (cellMap χ ≫ q).left).1
    have h' := congrArg (fun z => z.left) h
    simpa only [Over.comp_left, Category.assoc] using h'
  rw [ha]

/-- The cell is open in `Q`. -/
theorem isOpen_cell : IsOpen (cell χ q) := by
  have := isOpenImmersion_cell χ q hf
  exact (cellMap χ ≫ q).left.isOpenEmbedding.isOpen_range

omit hf [Flat q.left] [Surjective q.left] [QuasiCompact q.left] [Smooth G.X.hom]
  [IsAffineHom G.X.hom] in
/-- The image of a point of `U_G(χ⁻¹)` lies in the cell. -/
theorem range_subset_cell {T : Over (Spec (CommRingCat.of k))} {u : T ⟶ G.X}
    (hu : u ∈ (Dynamic.unipotent (opposite χ)).carrier T) :
    Set.range (u ≫ q).left ⊆ cell χ q := by
  rw [← (Affine.isRepresentedBy_unipotentHom (opposite χ)).2] at hu
  obtain ⟨a, rfl⟩ := SubgroupFunctor.mem_range.1 hu
  rintro _ ⟨t, rfl⟩
  exact ⟨a.left t, rfl⟩

omit hf [Flat q.left] [Surjective q.left] [QuasiCompact q.left] [Smooth G.X.hom]
  [IsAffineHom G.X.hom] in
/-- The image of the identity lies in the cell. -/
theorem range_one_subset_cell {T : Over (Spec (CommRingCat.of k))} :
    Set.range ((1 : T ⟶ G.X) ≫ q).left ⊆ cell χ q :=
  range_subset_cell χ q (one_mem _)

end Langlands.GroupScheme.Dynamic.OppositeCell
