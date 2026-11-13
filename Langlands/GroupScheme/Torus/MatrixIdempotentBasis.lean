import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Basis

/-! # A basis from columns of a complete family of orthogonal idempotents -/

noncomputable section
universe u v w

namespace Langlands.GroupScheme.MatrixIdempotentBasis

open Module
open scoped Matrix

variable {L : Type u} [Field L] {n : Type v} [Fintype n] [DecidableEq n]
  {M : Type w} (e : M → Matrix n n L)

/-- The column family of a family of matrices, indexed by matrix label and column. -/
def columnFamily (q : M × n) : n → L := (e q.1).col q.2

/-- Columns span the ambient vector space when a finite sum of the matrices is the identity. -/
theorem span_columnFamily (S : Finset M) (hsum : ∑ m ∈ S, e m = 1) :
    Submodule.span L (Set.range (columnFamily e)) = ⊤ := by
  classical
  apply top_unique
  rw [← (Pi.basisFun L n).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  have hcol : ∑ m ∈ S, columnFamily e (m, j) = Pi.basisFun L n j := by
    funext a
    have h := congrFun (congrFun hsum a) j
    simpa only [Finset.sum_apply, Matrix.sum_apply, columnFamily, Matrix.col_apply,
      Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply] using h
  rw [← hcol]
  exact Submodule.sum_mem _ (fun m _ => Submodule.subset_span (Set.mem_range_self (m, j)))

/-- Select a basis from the columns of a complete finite family. -/
theorem exists_columnBasis (S : Finset M) (hsum : ∑ m ∈ S, e m = 1) :
    ∃ (b : Basis n L (n → L)) (q : n → M × n),
      ∀ j, b j = columnFamily e (q j) := by
  classical
  let V := Set.range (columnFamily e)
  have hs : ⊤ ≤ Submodule.span L V := by
    rw [show Submodule.span L V = ⊤ from span_columnFamily e S hsum]
  let b' := Basis.ofSpan hs
  let f := b'.indexEquiv (Pi.basisFun L n)
  let b := b'.reindex f
  have hb (j : n) : b j ∈ V := by
    apply Basis.ofSpan_subset hs
    exact ⟨f.symm j, (b'.reindex_apply f j).symm⟩
  choose q hq using hb
  exact ⟨b, q, fun j => (hq j).symm⟩

variable [DecidableEq M]
  (hmul : ∀ m p, e m * e p = if m = p then e m else 0)

include hmul in
omit [DecidableEq n] in
/-- A matrix projector acts on a column of another projector by the Kronecker rule. -/
theorem mulVec_columnFamily (m : M) (q : M × n) :
    e m *ᵥ columnFamily e q = if m = q.1 then columnFamily e q else 0 := by
  change (e m * e q.1).col q.2 = _
  rw [hmul]
  by_cases h : m = q.1
  · simp only [h, ite_true, columnFamily]
  · simp only [h, ite_false]
    rfl

include hmul in
omit [DecidableEq n] in
/-- Every nonzero projector label occurs among the labels of any basis of projector columns. -/
theorem label_mem_range_of_ne_zero
    (b : Basis n L (n → L)) (q : n → M × n)
    (hb : ∀ j, b j = columnFamily e (q j)) {m : M} (hm : e m ≠ 0) :
    m ∈ Set.range (fun j => (q j).1) := by
  classical
  by_contra h
  have hneq (j : n) : m ≠ (q j).1 := by
    intro h'
    exact h ⟨j, h'.symm⟩
  have hz : (e m).mulVecLin = (0 : Matrix n n L).mulVecLin := by
    apply b.ext
    intro j
    simp only [Matrix.mulVecLin_apply, hb, mulVec_columnFamily e hmul, hneq,
      ite_false, Matrix.zero_mulVec]
  apply hm
  apply Matrix.mulVec_injective
  exact congrArg (fun f : (n → L) →ₗ[L] (n → L) => (f : (n → L) → (n → L))) hz

include hmul in
/-- A complete orthogonal family has a column basis in which every nonzero label occurs. -/
theorem exists_columnBasis_with_labels (S : Finset M) (hsum : ∑ m ∈ S, e m = 1) :
    ∃ (b : Basis n L (n → L)) (q : n → M × n),
      (∀ j, b j = columnFamily e (q j)) ∧
      ∀ m, e m ≠ 0 → m ∈ Set.range (fun j => (q j).1) := by
  obtain ⟨b, q, hb⟩ := exists_columnBasis e S hsum
  exact ⟨b, q, hb, fun _ hm => label_mem_range_of_ne_zero e hmul b q hb hm⟩

end Langlands.GroupScheme.MatrixIdempotentBasis
