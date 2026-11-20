import Langlands.Algebra.EnvelopingPositiveWeightLie
import Langlands.Representation.Geometric.WeylDefinitions

/-! # The relative enveloping projection for standard general linear blocks -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.Kostant

open Langlands.Algebra Langlands.Algebra.UniversalEnveloping Langlands.GeneralLinear Langlands.Geometric

attribute [local instance 100] LieRing.ofAssociativeRing

section DiagonalGrading

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

/-- The integral grading given by diagonal entries `-h i p`. -/
def diagonalAdjointWeight (h : ∀ i, Fin (n i) → ℤ) (a : Coord n) : ℤ :=
  h a.1 a.2.2 - h a.1 a.2.1

/-- The diagonal element inducing the given grading. -/
def diagonalGradingElement (h : ∀ i, Fin (n i) → ℤ) : GLProd ℂ n :=
  fun i => Matrix.diagonal fun p => -(h i p : ℂ)

/-- Each matrix unit is an eigenvector for the diagonal grading. -/
theorem lie_diagonalGradingElement_basis (h : ∀ i, Fin (n i) → ℤ) (a : Coord n) :
    ⁅diagonalGradingElement h, glBasis ℂ n a⁆ = (diagonalAdjointWeight h a : ℂ) • glBasis ℂ n a := by
  obtain ⟨i, p, q⟩ := a
  rw [glBasis_apply, lie_unit]
  simp only [diagonalGradingElement, Matrix.diagonal_apply, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true, diagonalAdjointWeight]
  rw [← sub_smul]
  congr 1
  push_cast
  ring

end DiagonalGrading

section Block

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n : ℕ} (B : BlockShape n)

/-- The factors in the block diagonal Levi product, one family per matrix place. -/
abbrev blockRanks (_ι : Type u) : _ι × Fin B.length → ℕ := fun i => B.size i.2

/-- The grading whose positive directions are precisely the strict upper block units. -/
def blockAdjointWeight (ι : Type u) : Coord (fun _ : ι => n) → ℤ :=
  diagonalAdjointWeight fun _ p => (blockIndex B p : ℤ)

omit [Fintype ι] [DecidableEq ι] in
theorem blockAdjointWeight_pos_iff (a : Coord (fun _ : ι => n)) :
    0 < blockAdjointWeight B ι a ↔ blockIndex B a.2.1 < blockIndex B a.2.2 := by
  change 0 < ((blockIndex B a.2.2 : ℕ) : ℤ) - ((blockIndex B a.2.1 : ℕ) : ℤ) ↔ _
  rw [sub_pos, Int.ofNat_lt, Fin.lt_def]

/-- The associative block diagonal map at each matrix place. -/
def blockMatrixInclusion : GLProd ℂ (blockRanks B ι) →ₐ[ℂ] GLProd ℂ (fun _ : ι => n) where
  __ := RingHom.pi fun i => (Matrix.reindexRingEquiv ℂ B.indexEquiv).toRingHom.comp
    ((Matrix.blockDiagonal'RingHom (fun j => Fin (B.size j)) ℂ).comp
      (RingHom.pi fun j => Pi.evalRingHom (fun a => Matrix (Fin (blockRanks B ι a))
        (Fin (blockRanks B ι a)) ℂ) (i, j)))
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one]
    funext i
    change Matrix.reindex B.indexEquiv B.indexEquiv
      (Matrix.blockDiagonal' (z • (1 : ∀ j, Matrix (Fin (B.size j)) (Fin (B.size j)) ℂ))) =
      z • (1 : Matrix (Fin n) (Fin n) ℂ)
    rw [Matrix.blockDiagonal'_smul, Matrix.blockDiagonal'_one]
    change (Matrix.reindexAlgEquiv ℂ ℂ B.indexEquiv) (z • 1) = _
    rw [map_smul, map_one]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem blockMatrixInclusion_apply (X : GLProd ℂ (blockRanks B ι)) (i : ι) :
    blockMatrixInclusion B X i = Matrix.reindex B.indexEquiv B.indexEquiv
      (Matrix.blockDiagonal' fun j => X (i, j)) := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem blockMatrixInclusion_apply_index (X : GLProd ℂ (blockRanks B ι)) (i : ι)
    (j : Fin B.length) (p q : Fin (B.size j)) :
    blockMatrixInclusion B X i (B.index j p) (B.index j q) = X (i, j) p q := by
  simp [BlockShape.index, Matrix.reindex_apply, Matrix.blockDiagonal'_apply_eq]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem blockMatrixInclusion_apply_index_ne (X : GLProd ℂ (blockRanks B ι)) (i : ι)
    {j k : Fin B.length} (h : j ≠ k) (p : Fin (B.size j)) (q : Fin (B.size k)) :
    blockMatrixInclusion B X i (B.index j p) (B.index k q) = 0 := by
  simp [BlockShape.index, Matrix.reindex_apply, Matrix.blockDiagonal'_apply_ne (fun a => X (i, a)) p q h]

/-- Relabel the matrix coordinates of the Levi inside the ambient algebra. -/
def blockCoord (a : Coord (blockRanks B ι)) : Coord (fun _ : ι => n) :=
  ⟨a.1.1, B.index a.1.2 a.2.1, B.index a.1.2 a.2.2⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem blockAdjointWeight_blockCoord (a : Coord (blockRanks B ι)) :
    blockAdjointWeight B ι (blockCoord B a) = 0 := by
  simp [blockAdjointWeight, diagonalAdjointWeight, blockCoord]

/-- The weight-zero indices are exactly the matrix coordinates of the block Levi. -/
def blockZeroCoordEquiv : Coord (blockRanks B ι) ≃ {a // blockAdjointWeight B ι a = 0} :=
  Equiv.ofBijective (fun a => ⟨blockCoord B a, blockAdjointWeight_blockCoord B a⟩) (by
    constructor
    · rintro ⟨⟨i, j⟩, p, q⟩ ⟨⟨i', j'⟩, p', q'⟩ h
      have hcoord := congrArg Subtype.val h
      change (⟨i, B.index j p, B.index j q⟩ : Coord (fun _ : ι => n)) =
        ⟨i', B.index j' p', B.index j' q'⟩ at hcoord
      have hi : i = i' := congrArg Sigma.fst hcoord
      subst i'
      have hrows := congrArg (fun a => a.2.1) hcoord
      have hcols := congrArg (fun a => a.2.2) hcoord
      have hj : j = j' := by simpa using congrArg (blockIndex B) hrows
      subst j'
      rw [(B.index j).injective hrows, (B.index j).injective hcols]
    · rintro ⟨⟨i, p, q⟩, h⟩
      have he : blockIndex B p = blockIndex B q := by
        change ((blockIndex B q : ℕ) : ℤ) - ((blockIndex B p : ℕ) : ℤ) = 0 at h
        apply Fin.ext
        omega
      let x := B.indexEquiv.symm p
      let y := B.indexEquiv.symm q
      have hxy : x.1 = y.1 := he
      let y' : Fin (B.size x.1) := cast (congrArg (fun j => Fin (B.size j)) hxy.symm) y.2
      have hp : B.index x.1 x.2 = p := B.indexEquiv.apply_symm_apply p
      have hy : (⟨x.1, y'⟩ : B.Index) = y := by
        refine Sigma.ext (x := (⟨x.1, y'⟩ : B.Index)) (y := y) hxy ?_
        exact cast_heq _ _
      have hq : B.index x.1 y' = q :=
        (congrArg B.indexEquiv hy).trans (B.indexEquiv.apply_symm_apply q)
      refine ⟨⟨(i, x.1), x.2, y'⟩, Subtype.ext ?_⟩
      change (⟨i, B.index x.1 x.2, B.index x.1 y'⟩ : Coord (fun _ : ι => n)) = ⟨i, p, q⟩
      rw [hp, hq])

/-- A block matrix unit maps to the corresponding ambient matrix unit. -/
theorem blockMatrixInclusion_basis (a : Coord (blockRanks B ι)) :
    blockMatrixInclusion B (glBasis ℂ (blockRanks B ι) a) =
      glBasis ℂ (fun _ : ι => n) (blockCoord B a) := by
  obtain ⟨⟨i, j⟩, p, q⟩ := a
  rw [glBasis_apply, glBasis_apply]
  funext i'
  ext r s
  obtain ⟨⟨k, r⟩, rfl⟩ := B.indexEquiv.surjective r
  obtain ⟨⟨l, s⟩, rfl⟩ := B.indexEquiv.surjective s
  change blockMatrixInclusion B (unit ℂ (blockRanks B ι) (i, j) p q) i'
      (B.index k r) (B.index l s) =
    unit ℂ (fun _ : ι => n) i (B.index j p) (B.index j q) i' (B.index k r) (B.index l s)
  change _ = unit ℂ (fun _ : ι => n) i (B.index j p) (B.index j q)
    (⟨i', B.index k r, B.index l s⟩ : Coord (fun _ : ι => n)).1
    (⟨i', B.index k r, B.index l s⟩ : Coord (fun _ : ι => n)).2.1
    (⟨i', B.index k r, B.index l s⟩ : Coord (fun _ : ι => n)).2.2
  rw [unit_apply]
  by_cases hkl : k = l
  · subst l
    rw [blockMatrixInclusion_apply_index]
    change unit ℂ (blockRanks B ι) (i, j) p q
      (⟨(i', k), r, s⟩ : Coord (blockRanks B ι)).1
      (⟨(i', k), r, s⟩ : Coord (blockRanks B ι)).2.1
      (⟨(i', k), r, s⟩ : Coord (blockRanks B ι)).2.2 = _
    rw [unit_apply]
    by_cases hkj : k = j
    · subst j
      simp [Prod.mk.injEq, Sigma.mk.injEq, (B.index k).injective.eq_iff]
    · have hrow : B.index k r ≠ B.index j p := fun e => hkj (by
        simpa using congrArg (blockIndex B) e)
      simp [hkj, hrow, Prod.mk.injEq, Sigma.mk.injEq]
  · rw [blockMatrixInclusion_apply_index_ne B _ i' hkl]
    symm
    apply ite_eq_right_iff.mpr
    intro he
    have hr := congrArg (fun a : Coord (fun _ : ι => n) => blockIndex B a.2.1) he
    have hs := congrArg (fun a : Coord (fun _ : ι => n) => blockIndex B a.2.2) he
    exact (hkl ((by simpa using hr : k = j).trans (by simpa using hs.symm : j = l))).elim

/-- The central congruence for a standard block parabolic, with its actual strictly upper
block right ideal and actual block diagonal Lie inclusion. -/
def blockEnvelopingDecomposition :
    RelativeEnvelopingDecomposition (Langlands.Algebra.LieEnvelopingEquiv.map
      (blockMatrixInclusion B (ι := ι)).toLieHom) := by
  let b := glBasis ℂ (fun _ : ι => n)
  let d := blockAdjointWeight B ι
  let H := diagonalGradingElement (fun _ : ι => fun p => (blockIndex B p : ℤ))
  let hH : ∀ a, ⁅H, b a⁆ = (d a : ℂ) • b a := lie_diagonalGradingElement_basis _
  let P := positiveWeightLieSubalgebra b d H hH
  let c₀ := (glBasis ℂ (blockRanks B ι)).reindex (blockZeroCoordEquiv B)
  refine relativeEnvelopingDecomposition_of_weight b d (blockMatrixInclusion B).toLieHom
    P.incl c₀ (positiveWeightLieBasis b d H hH) ?_ (positiveWeightLieSubalgebra_incl_basis b d H hH)
    H hH
  intro a
  change blockMatrixInclusion B ((glBasis ℂ (blockRanks B ι)).reindex (blockZeroCoordEquiv B) a) = b a.val
  rw [Module.Basis.reindex_apply, blockMatrixInclusion_basis]
  rw [show blockCoord B ((blockZeroCoordEquiv B).symm a) = a.val from
    congrArg Subtype.val ((blockZeroCoordEquiv B).apply_symm_apply a)]

theorem blockEnvelopingDecomposition_ideal :
    (blockEnvelopingDecomposition B (ι := ι)).ideal =
      positiveWeightRightIdeal (glBasis ℂ (fun _ : ι => n)) (blockAdjointWeight B ι) := rfl

end Block

end Langlands.Archimedean.Kostant
