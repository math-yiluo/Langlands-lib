import Langlands.Group.GL.UpperBruhatStatement
import Langlands.Group.GL.UpperBruhatEmbedding
import Langlands.Group.GL.UpperBruhatPivotProof

namespace Langlands.GeneralLinear

universe u

namespace Bruhat

variable {R : Type u} [CommRing R] {n : ℕ}

@[simp] theorem insert_last_last (g : Langlands.GeneralLinear n R) :
    insert (Fin.last n) g (Fin.last n) (Fin.last n) = 1 := insert_p_p _ _

@[simp] theorem insert_last_castSucc (g : Langlands.GeneralLinear n R) (i : Fin n) :
    insert (Fin.last n) g (Fin.last n) i.castSucc = 0 := by
  rw [← Fin.succAbove_last]
  exact insert_p_succAbove _ _ _

@[simp] theorem insert_castSucc_last (g : Langlands.GeneralLinear n R) (i : Fin n) :
    insert (Fin.last n) g i.castSucc (Fin.last n) = 0 := by
  rw [← Fin.succAbove_last]
  exact insert_succAbove_p _ _ _

@[simp] theorem insert_castSucc_castSucc (g : Langlands.GeneralLinear n R) (i j : Fin n) :
    insert (Fin.last n) g i.castSucc j.castSucc = g i j := by
  rw [← Fin.succAbove_last]
  exact insert_succAbove_succAbove _ _ _ _

/-- The entry formulas for lifting two smaller Bruhat factors across an isolated pivot. -/
theorem lifted_entries (a b : Langlands.GeneralLinear n R) (w : Equiv.Perm (Fin n))
    (p : Fin (n + 1)) :
    let G := insert (Fin.last n) a * permutation (n + 1) R (extendPerm p w) * insert p b
    (∀ j : Fin (n + 1), G (Fin.last n) j = if j = p then 1 else 0) ∧
    (∀ i : Fin n, G i.castSucc p = 0) ∧
    (∀ i j : Fin n, G i.castSucc (p.succAbove j) =
      (a * permutation n R w * b) i j) := by
  dsimp only
  have hmul (i j : Fin (n + 1)) :
      (insert (Fin.last n) a * permutation (n + 1) R (extendPerm p w) * insert p b) i j =
      insert (Fin.last n) a i (Fin.last n) * insert p b p j +
        ∑ k : Fin n, insert (Fin.last n) a i (w k).castSucc * insert p b (p.succAbove k) j := by
    change ((insert (Fin.last n) a * permutation (n + 1) R (extendPerm p w)).val *
      (insert p b).val) i j = _
    rw [Matrix.mul_apply, Fin.sum_univ_succAbove _ p]
    simp only [mul_permutation_entry, extendPerm_p, extendPerm_succAbove]
  constructor
  · intro j
    induction j using Fin.succAboveCases p with
    | x => simp [hmul, finSuccEquiv'_last_apply_castSucc]
    | p j => simp [hmul, Fin.succAbove_ne, finSuccEquiv'_last_apply_castSucc]
  constructor
  · intro i
    simp [hmul, finSuccEquiv'_last_apply_castSucc]
  · intro i j
    rw [hmul]
    simp only [insert_castSucc_last, insert_p_succAbove, mul_zero, zero_add,
      insert_castSucc_castSucc, insert_succAbove_succAbove]
    change _ = ((a * permutation n R w).val * b.val) i j
    simp only [Matrix.mul_apply, mul_permutation_entry]

/-- Recover a larger factorization from the factorization of its complementary minor. -/
theorem factor_of_isolated_pivot (g : Langlands.GeneralLinear (n + 1) R)
    (p : Fin (n + 1)) (h : Langlands.GeneralLinear n R)
    (hrow : ∀ j : Fin (n + 1), g (Fin.last n) j = if j = p then 1 else 0)
    (hcol : ∀ i : Fin n, g i.castSucc p = 0)
    (hminor : ∀ i j : Fin n, g i.castSucc (p.succAbove j) = h i j)
    (a b : Langlands.GeneralLinear n R) (w : Equiv.Perm (Fin n))
    (ha : ∀ i j : Fin n, j < i → a i j = 0)
    (hb : ∀ i j : Fin n, j < i → b i j = 0)
    (heq : h = a * permutation n R w * b) :
    ∃ (A B : Langlands.GeneralLinear (n + 1) R) (W : Equiv.Perm (Fin (n + 1))),
      (∀ i j, j < i → A i j = 0) ∧ (∀ i j, j < i → B i j = 0) ∧
      g = A * permutation (n + 1) R W * B := by
  refine ⟨insert (Fin.last n) a, insert p b, extendPerm p w,
    insert_upper _ _ ha, insert_upper _ _ hb, ?_⟩
  obtain ⟨hr, hc, hm⟩ := lifted_entries a b w p
  apply Units.ext
  ext i j
  induction i using Fin.lastCases with
  | last => exact (hrow j).trans (hr j).symm
  | cast i =>
    induction j using Fin.succAboveCases p with
    | x => exact (hcol i).trans (hc i).symm
    | p j => rw [hminor, heq, hm]

end Bruhat

/-- The rank induction, conditional only on the focused pivot-isolation theorem. -/
theorem fieldUpperBruhatFactorization_of_pivot
    (pivot : FieldUpperBruhatPivotTheorem.{u}) :
    FieldUpperBruhatFactorizationTheorem.{u} := by
  intro K _ n
  induction n with
  | zero =>
    intro g
    refine ⟨1, 1, Equiv.refl _, ?_, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · apply Units.ext
      ext i
      exact Fin.elim0 i
  | succ n ih =>
    intro g
    obtain ⟨L, R, p, h, hL, hR, hrow, hcol, hminor⟩ := pivot K n g
    obtain ⟨a, b, w, ha, hb, heq⟩ := ih h
    obtain ⟨A, B, W, hA, hB, hfactor⟩ :=
      Bruhat.factor_of_isolated_pivot (L * g * R) p h hrow hcol hminor a b w ha hb heq
    refine ⟨L⁻¹ * A, B * R⁻¹, W, ?_, ?_, ?_⟩
    · exact (upperTriangularSubgroup (n + 1) K).mul_mem
        ((upperTriangularSubgroup (n + 1) K).inv_mem hL) hA
    · exact (upperTriangularSubgroup (n + 1) K).mul_mem hB
        ((upperTriangularSubgroup (n + 1) K).inv_mem hR)
    · have h := congrArg (fun x => L⁻¹ * x * R⁻¹) hfactor
      simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using h

/-- Upper triangular Bruhat factorization over every field and in every natural rank. -/
theorem fieldUpperBruhatFactorizationTheorem : FieldUpperBruhatFactorizationTheorem.{u} :=
  fieldUpperBruhatFactorization_of_pivot fieldUpperBruhatPivotTheorem

end Langlands.GeneralLinear
