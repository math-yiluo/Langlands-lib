import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-! # Simple coroot coordinates on the special linear diagonal torus -/

namespace Langlands.KazhdanPatterson

open Matrix (SpecialLinearGroup)

universe u

variable {r : ℕ} {U : Type u} [CommGroup U]

/-- Unit tuples of length `r + 1` whose entries multiply to one. -/
def detOneDiagonal (r : ℕ) (U : Type u) [CommGroup U] : Subgroup (Fin (r + 1) → U) :=
  (∏ i, Pi.evalMonoidHom (fun _ : Fin (r + 1) => U) i).ker

@[simp]
theorem mem_detOneDiagonal (t : Fin (r + 1) → U) :
    t ∈ detOneDiagonal r U ↔ ∏ i, t i = 1 := by
  simp only [detOneDiagonal, MonoidHom.mem_ker, MonoidHom.finsetProd_apply, Pi.evalMonoidHom_apply]

private theorem partialProd_last {n : ℕ} (t : Fin n → U) :
    Fin.partialProd t (Fin.last n) = ∏ i, t i := by
  rw [Fin.partialProd]
  simp [List.take_of_length_le, Fin.prod_ofFn]

private theorem partialProd_mul {n : ℕ} (t s : Fin n → U) (j : Fin (n + 1)) :
    Fin.partialProd (t * s) j = Fin.partialProd t j * Fin.partialProd s j := by
  refine Fin.inductionOn j (by simp) ?_
  intro i ih
  simp only [Fin.partialProd_succ, Pi.mul_apply, ih]
  exact mul_mul_mul_comm _ _ _ _

private def endpointPrefixes (x : Fin r → U) : Fin (r + 2) → U :=
  Fin.cons 1 (Fin.snoc x 1)

private def adjacentRatios (x : Fin r → U) (j : Fin (r + 1)) : U :=
  (endpointPrefixes x j.castSucc)⁻¹ * endpointPrefixes x j.succ

private theorem partialProd_adjacentRatios (x : Fin r → U) :
    Fin.partialProd (adjacentRatios x) = endpointPrefixes x := by
  have h := Fin.partialProd_left_inv (endpointPrefixes x)
  rw [show endpointPrefixes x 0 = 1 from rfl, one_smul] at h
  exact h

/-- The coordinates of a determinant-one diagonal in the ordered simple coroots.
The coordinate of `i` is the product up to and including the entry at `i.castSucc`. -/
def simpleCorootCoordinates (r : ℕ) (U : Type u) [CommGroup U] :
    detOneDiagonal r U ≃* (Fin r → U) where
  toFun t i := Fin.partialProd t.val i.castSucc.succ
  invFun x := ⟨adjacentRatios x, by
    rw [mem_detOneDiagonal, ← partialProd_last, partialProd_adjacentRatios]
    rw [← Fin.succ_last, endpointPrefixes, Fin.cons_succ, Fin.snoc_last]⟩
  left_inv t := by
    apply Subtype.ext
    change adjacentRatios (fun i => Fin.partialProd t.val i.castSucc.succ) = t.val
    have hprefix : endpointPrefixes (fun i => Fin.partialProd t.val i.castSucc.succ) =
        Fin.partialProd t.val := by
      funext j
      refine Fin.cases (by simp [endpointPrefixes]) (fun k => ?_) j
      rw [endpointPrefixes, Fin.cons_succ]
      refine Fin.lastCases ?_ (fun i => ?_) k
      · rw [Fin.snoc_last, Fin.succ_last, partialProd_last]
        exact (mem_detOneDiagonal t.val).mp t.property |>.symm
      · rw [Fin.snoc_castSucc]
    funext j
    rw [adjacentRatios, hprefix, Fin.partialProd_right_inv]
  right_inv x := by
    funext i
    change Fin.partialProd (adjacentRatios x) i.castSucc.succ = x i
    rw [partialProd_adjacentRatios, endpointPrefixes, Fin.cons_succ, Fin.snoc_castSucc]
  map_mul' t s := by
    funext i
    exact partialProd_mul t.val s.val i.castSucc.succ

private theorem snoc_mulSingle (i : Fin r) (x : U) :
    (Fin.snoc (Pi.mulSingle i x) 1 : Fin (r + 1) → U) = Pi.mulSingle i.castSucc x := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · rw [Fin.snoc_last, Pi.mulSingle_eq_of_ne (Fin.castSucc_ne_last i).symm]
  · simp [Pi.mulSingle_apply]

private theorem cons_mulSingle (i : Fin r) (x : U) :
    (Fin.cons 1 (Pi.mulSingle i x) : Fin (r + 1) → U) = Pi.mulSingle i.succ x := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [Fin.cons_zero, Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero i).symm]
  · simp [Pi.mulSingle_apply]

/-- The inverse coordinates of a single parameter put `x` and `x⁻¹` in adjacent positions. -/
theorem simpleCorootCoordinates_symm_mulSingle (i : Fin r) (x : U) :
    ((simpleCorootCoordinates r U).symm (Pi.mulSingle i x)).val =
      Pi.mulSingle i.castSucc x * Pi.mulSingle i.succ x⁻¹ := by
  funext j
  change adjacentRatios (Pi.mulSingle i x) j = _
  have hleft (z : Fin r → U) :
      endpointPrefixes z j.castSucc = (Fin.cons 1 z : Fin (r + 1) → U) j := by
    refine Fin.cases (by simp [endpointPrefixes]) (fun k => ?_) j
    rw [Fin.castSucc_succ, endpointPrefixes, Fin.cons_succ, Fin.snoc_castSucc, Fin.cons_succ]
  rw [adjacentRatios, hleft, endpointPrefixes, Fin.cons_succ, snoc_mulSingle, cons_mulSingle,
    Pi.mul_apply, mul_comm]
  exact congrArg (fun t : Fin (r + 1) → U =>
    Pi.mulSingle (M := fun _ : Fin (r + 1) => U) i.castSucc x j * t j)
    ((MonoidHom.mulSingle (fun _ : Fin (r + 1) => U) i.succ).map_inv x).symm

/-- Reconstruct the determinant-one diagonal as the product of its simple coroot factors. -/
theorem simpleCorootCoordinates_symm_eq_prod (x : Fin r → U) :
    (simpleCorootCoordinates r U).symm x =
      ∏ i, (simpleCorootCoordinates r U).symm (Pi.mulSingle i (x i)) := by
  conv_lhs => rw [← Finset.univ_prod_mulSingle x]
  exact map_prod (simpleCorootCoordinates r U).symm _ _

variable (r) (F : Type u) [Field F]

/-- Form the actual special linear matrix from determinant-one unit coordinates. -/
def slDiagonalMatrix : detOneDiagonal r Fˣ →* SpecialLinearGroup (Fin (r + 1)) F where
  toFun t := ⟨Matrix.diagonal (fun i => (t.val i : F)), by
    rw [Matrix.det_diagonal]
    change (∏ i, Units.coeHom F (t.val i)) = 1
    rw [← map_prod (Units.coeHom F)]
    rw [(mem_detOneDiagonal t.val).mp t.property, map_one]⟩
  map_one' := Subtype.ext Matrix.diagonal_one
  map_mul' t s := by
    apply Subtype.ext
    exact (Matrix.diagonal_mul_diagonal _ _).symm

theorem slDiagonalMatrix_injective : Function.Injective (slDiagonalMatrix r F) := by
  intro t s h
  apply Subtype.ext
  funext i
  apply Units.ext
  have he := congrArg (fun g : SpecialLinearGroup (Fin (r + 1)) F => g.val i i) h
  change Matrix.diagonal (fun j => (t.val j : F)) i i =
    Matrix.diagonal (fun j => (s.val j : F)) i i at he
  simpa only [Matrix.diagonal_apply_eq] using he

/-- The diagonal subgroup of the actual special linear group. -/
def slDiagonalTorus : Subgroup (SpecialLinearGroup (Fin (r + 1)) F) :=
  (slDiagonalMatrix r F).range

theorem mem_slDiagonalTorus (g : SpecialLinearGroup (Fin (r + 1)) F) :
    g ∈ slDiagonalTorus r F ↔ g.val.IsDiag := by
  constructor
  · rintro ⟨t, rfl⟩
    exact Matrix.isDiag_diagonal _
  · intro hg
    have hprod : ∏ i, g.val i i = 1 := by
      rw [← Matrix.det_diagonal, show Matrix.diagonal (fun i => g.val i i) = g.val from
        hg.diagonal_diag]
      exact g.property
    have hnz : ∏ i, g.val i i ≠ 0 := by rw [hprod]; exact one_ne_zero
    let t (i : Fin (r + 1)) : Fˣ :=
      Units.mk0 (g.val i i) (Finset.prod_ne_zero_iff.mp hnz i (Finset.mem_univ i))
    have ht : t ∈ detOneDiagonal r Fˣ := by
      rw [mem_detOneDiagonal]
      apply Units.ext
      exact (map_prod (Units.coeHom F) t Finset.univ).trans hprod
    exact ⟨⟨t, ht⟩, Subtype.ext hg.diagonal_diag⟩

/-- Simple coroot parameters identify the determinant-one diagonal subgroup with a product of units. -/
noncomputable def slDiagonalCorootEquiv :
    (Fin r → Fˣ) ≃* slDiagonalTorus r F :=
  (simpleCorootCoordinates r Fˣ).symm.trans (MonoidHom.ofInjective (slDiagonalMatrix_injective r F))

end Langlands.KazhdanPatterson
