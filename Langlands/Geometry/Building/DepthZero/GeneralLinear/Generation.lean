import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Generation of `GL_n(R)` and of the Iwahori subgroup over a local ring

Let `R` be a commutative local ring. A subgroup of `GL_n(R)` containing the invertible diagonal
matrices and all elementary transvections `1 + c E_{ij}` is the whole group
(`eq_top_of_diagUnit_transvectionUnit_mem`). A subgroup containing the invertible diagonal
matrices, the transvections `1 + c E_{ij}` with `i < j`, and those with `i > j` and `c` in the
maximal ideal contains every invertible matrix whose entries below the diagonal lie in the
maximal ideal (`mem_of_iwahori`).

The proof is Gaussian elimination by columns: for a matrix whose first `k` columns are already
diagonal, some entry of column `k` on or below the diagonal is a unit (otherwise the matrix
would not be invertible over the local ring); it is moved to the diagonal by adding a row, and
the other entries of column `k` are cleared by row operations with that pivot.
-/

noncomputable section

open Matrix

namespace Langlands.Geometry.Building.GeneralLinearParahoric

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The elementary transvection `1 + c E_{ij}` in `GL_n(R)`. -/
def transvectionUnit {i j : Fin n} (hij : i ≠ j) (c : R) : GL (Fin n) R :=
  Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij c)

theorem coe_transvectionUnit {i j : Fin n} (hij : i ≠ j) (c : R) :
    (transvectionUnit hij c : Matrix (Fin n) (Fin n) R) = Matrix.transvection i j c :=
  rfl

/-- The invertible diagonal matrix with diagonal `d`. -/
def diagUnit (d : Fin n → Rˣ) : GL (Fin n) R where
  val := diagonal fun k => (d k : R)
  inv := diagonal fun k => ((d k)⁻¹ : Rˣ)
  val_inv := by rw [diagonal_mul_diagonal]; simp
  inv_val := by rw [diagonal_mul_diagonal]; simp

theorem coe_diagUnit (d : Fin n → Rˣ) :
    (diagUnit d : Matrix (Fin n) (Fin n) R) = diagonal fun k => (d k : R) :=
  rfl

/-- The entries of `(1 + c E_{ij}) g`: row `i` becomes row `i` plus `c` times row `j`. -/
theorem transvectionUnit_mul_apply {i j : Fin n} (hij : i ≠ j) (c : R) (g : GL (Fin n) R)
    (p q : Fin n) :
    ((transvectionUnit hij c * g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p q =
      if p = i then (g : Matrix (Fin n) (Fin n) R) i q + c * (g : Matrix (Fin n) (Fin n) R) j q
      else (g : Matrix (Fin n) (Fin n) R) p q := by
  rw [Units.val_mul, coe_transvectionUnit]
  split_ifs with hp
  · subst hp
    exact transvection_mul_apply_same _ _ _ _ _
  · exact transvection_mul_apply_of_ne _ _ _ _ hp _ _

/-- The first `k` columns of `g` are diagonal. -/
def ColumnsCleared (g : Matrix (Fin n) (Fin n) R) (k : ℕ) : Prop :=
  ∀ j : Fin n, j.val < k → ∀ i, i ≠ j → g i j = 0

theorem isUnit_apply_self_of_columnsCleared (g : GL (Fin n) R) {k : ℕ}
    (hg : ColumnsCleared (g : Matrix (Fin n) (Fin n) R) k) {j : Fin n} (hj : j.val < k) :
    IsUnit ((g : Matrix (Fin n) (Fin n) R) j j) := by
  have h : ((g⁻¹ * g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) j j = 1 := by simp
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single j] at h
  · exact isUnit_of_mul_isUnit_right (h ▸ isUnit_one)
  · intro b _ hb
    rw [hg j hj b hb, mul_zero]
  · simp

variable [IsLocalRing R]

/-- In a matrix whose first `k` columns are diagonal, column `k` has a unit entry on or below
the diagonal. -/
theorem exists_isUnit_of_columnsCleared (g : GL (Fin n) R) {k : ℕ}
    (hg : ColumnsCleared (g : Matrix (Fin n) (Fin n) R) k) (hk : k < n) :
    ∃ i : Fin n, k ≤ i.val ∧ IsUnit ((g : Matrix (Fin n) (Fin n) R) i ⟨k, hk⟩) := by
  set kk : Fin n := ⟨k, hk⟩
  have hzero : ∀ i : Fin n, i.val < k →
      ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) kk i = 0 := by
    intro i hi
    have hne : kk ≠ i := fun h => by rw [← h] at hi; exact lt_irrefl _ hi
    have h : ((g⁻¹ * g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) kk i = 0 := by
      rw [inv_mul_cancel, Units.val_one, one_apply_ne hne]
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i] at h
    · exact (isUnit_apply_self_of_columnsCleared g hg hi).mul_left_eq_zero.1 h
    · intro b _ hb
      rw [hg i hi b hb, mul_zero]
    · simp
  have hsum : IsUnit (∑ i, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) kk i *
      (g : Matrix (Fin n) (Fin n) R) i kk) := by
    rw [← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_apply_eq]
    exact isUnit_one
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum hsum
  refine ⟨i, ?_, isUnit_of_mul_isUnit_right hi⟩
  by_contra hlt
  push Not at hlt
  rw [hzero i hlt, zero_mul] at hi
  exact not_isUnit_zero hi

variable (H : Subgroup (GL (Fin n) R))

omit [IsLocalRing R] in
/-- A subgroup containing the invertible diagonal matrices contains every matrix whose columns
are all diagonal. -/
theorem mem_of_columnsCleared_all (hdiag : ∀ d : Fin n → Rˣ, diagUnit d ∈ H) (g : GL (Fin n) R)
    (hg : ColumnsCleared (g : Matrix (Fin n) (Fin n) R) n) : g ∈ H := by
  have hu : ∀ j : Fin n, IsUnit ((g : Matrix (Fin n) (Fin n) R) j j) := fun j =>
    isUnit_apply_self_of_columnsCleared g hg j.isLt
  have hgd : g = diagUnit fun j => (hu j).unit := by
    ext p q : 2
    rw [coe_diagUnit, diagonal_apply]
    split_ifs with hpq
    · subst hpq
      rfl
    · exact hg q q.isLt p hpq
  rw [hgd]
  exact hdiag _

omit [IsLocalRing R] in
/-- **Clearing one column.** If the first `k` columns of `g` are diagonal and its entry `(k, k)`
is a unit `u`, and `H` contains the transvections `1 − g_{ik} u⁻¹ E_{ik}`, then some `h ∈ H`
makes the first `k + 1` columns of `h g` diagonal. Any property `Inv` preserved by these row
operations passes from `g` to `h g`. -/
theorem exists_mul_columnsCleared_succ (Inv : GL (Fin n) R → Prop) {k : ℕ} (hk : k < n)
    (g : GL (Fin n) R) (hg : ColumnsCleared (g : Matrix (Fin n) (Fin n) R) k)
    (u : Rˣ) (hu : (g : Matrix (Fin n) (Fin n) R) ⟨k, hk⟩ ⟨k, hk⟩ = u)
    (hT : ∀ i (hi : i ≠ (⟨k, hk⟩ : Fin n)),
      transvectionUnit hi (-(g : Matrix (Fin n) (Fin n) R) i ⟨k, hk⟩ * ↑u⁻¹) ∈ H)
    (hInv : ∀ M : GL (Fin n) R, Inv M → ∀ i (hi : i ≠ (⟨k, hk⟩ : Fin n)),
      Inv (transvectionUnit hi (-(g : Matrix (Fin n) (Fin n) R) i ⟨k, hk⟩ * ↑u⁻¹) * M))
    (hInvg : Inv g) :
    ∃ h ∈ H, ColumnsCleared ((h * g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) (k + 1) ∧
      Inv (h * g) := by
  set kk : Fin n := ⟨k, hk⟩
  -- Clear the rows of a finite set `S` not containing `k`.
  have key : ∀ S : Finset (Fin n), kk ∉ S → ∃ h ∈ H,
      (∀ q, ((h * g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) kk q =
        (g : Matrix (Fin n) (Fin n) R) kk q) ∧
      (∀ i ∈ S, ((h * g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i kk = 0) ∧
      (∀ i ∉ S, ((h * g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i kk =
        (g : Matrix (Fin n) (Fin n) R) i kk) ∧
      ColumnsCleared ((h * g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) k ∧ Inv (h * g) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, H.one_mem, fun q => by simp, fun i hi => absurd hi (Finset.notMem_empty i),
        fun i _ => by simp, by simpa using hg, by simpa using hInvg⟩
    | insert i S hiS ih =>
      intro hkS
      have hik : i ≠ kk := fun h => hkS (h ▸ Finset.mem_insert_self _ _)
      have hkS' : kk ∉ S := fun h => hkS (Finset.mem_insert_of_mem h)
      obtain ⟨h, hh, hrow, hzero, hsame, hclr, hinv⟩ := ih hkS'
      refine ⟨transvectionUnit hik (-(g : Matrix (Fin n) (Fin n) R) i kk * ↑u⁻¹) * h,
        H.mul_mem (hT i hik) hh, ?_, ?_, ?_, ?_, ?_⟩
      · intro q
        rw [mul_assoc, transvectionUnit_mul_apply, ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm hik)), hrow]
      · intro i' hi'
        rw [mul_assoc, transvectionUnit_mul_apply]
        rcases Finset.mem_insert.1 hi' with rfl | hi'S
        · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), hsame i' hiS, hrow, hu]
          simp
        · have hne : i' ≠ i := fun h => hiS (h ▸ hi'S)
          rw [ite_eq_right_of_eq_false _ _ (eq_false hne), hzero i' hi'S]
      · intro i' hi'
        have hne : i' ≠ i := fun h => hi' (h ▸ Finset.mem_insert_self _ _)
        rw [mul_assoc, transvectionUnit_mul_apply, ite_eq_right_of_eq_false _ _ (eq_false hne),
          hsame i' (fun h => hi' (Finset.mem_insert_of_mem h))]
      · intro j hj i' hi'j
        rw [mul_assoc, transvectionUnit_mul_apply]
        split_ifs with hi'
        · subst hi'
          have hkj : kk ≠ j := fun h => by
            rw [← h] at hj
            exact lt_irrefl _ hj
          rw [hclr j hj i' hi'j, hclr j hj kk hkj, mul_zero, add_zero]
        · exact hclr j hj i' hi'j
      · rw [mul_assoc]
        exact hInv _ hinv i hik
  obtain ⟨h, hh, hrow, hzero, -, hclr, hinv⟩ := key (Finset.univ.erase kk)
    (Finset.notMem_erase _ _)
  refine ⟨h, hh, ?_, hinv⟩
  intro j hj i hij
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjk | hjk
  · exact hclr j hjk i hij
  · have hj' : j = kk := Fin.ext hjk
    subst hj'
    exact hzero i (Finset.mem_erase.2 ⟨hij, Finset.mem_univ _⟩)

/-- **Generation of `GL_n(R)`.** Over a local ring, the invertible diagonal matrices and the
elementary transvections generate `GL_n(R)`. -/
theorem eq_top_of_diagUnit_transvectionUnit_mem (hdiag : ∀ d : Fin n → Rˣ, diagUnit d ∈ H)
    (htr : ∀ {i j : Fin n} (hij : i ≠ j) (c : R), transvectionUnit hij c ∈ H) : H = ⊤ := by
  rw [eq_top_iff]
  intro g _
  -- downward induction on the number of diagonal columns
  have main : ∀ m k, n - k = m → ∀ g : GL (Fin n) R,
      ColumnsCleared (g : Matrix (Fin n) (Fin n) R) k → g ∈ H := by
    intro m
    induction m with
    | zero =>
      intro k hk g hg
      exact mem_of_columnsCleared_all H hdiag g fun j hj => hg j (by omega)
    | succ m ih =>
      intro k hkm g hg
      have hk : k < n := by omega
      set kk : Fin n := ⟨k, hk⟩
      obtain ⟨i₀, hi₀k, hi₀⟩ := exists_isUnit_of_columnsCleared g hg hk
      -- move a unit to the diagonal
      obtain ⟨g', hg'H, hg'cl, hg'u⟩ : ∃ g' : GL (Fin n) R, (g' ∈ H → g ∈ H) ∧
          ColumnsCleared (g' : Matrix (Fin n) (Fin n) R) k ∧
          IsUnit ((g' : Matrix (Fin n) (Fin n) R) kk kk) := by
        by_cases hkk : IsUnit ((g : Matrix (Fin n) (Fin n) R) kk kk)
        · exact ⟨g, id, hg, hkk⟩
        · have hne : kk ≠ i₀ := fun h => by subst h; exact hkk hi₀
          refine ⟨transvectionUnit hne 1 * g, fun h' => ?_, ?_, ?_⟩
          · simpa using H.mul_mem (H.inv_mem (htr hne 1)) h'
          · intro j hj i hij
            rw [transvectionUnit_mul_apply]
            split_ifs with hi
            · subst hi
              have hij0 : i₀ ≠ j := fun h => by rw [← h] at hj; omega
              rw [hg j hj _ hij, hg j hj i₀ hij0, mul_zero, add_zero]
            · exact hg j hj i hij
          · rw [transvectionUnit_mul_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl), one_mul]
            have hs : IsUnit (((g : Matrix (Fin n) (Fin n) R) kk kk +
                (g : Matrix (Fin n) (Fin n) R) i₀ kk) + -(g : Matrix (Fin n) (Fin n) R) kk kk) := by
              simpa using hi₀
            exact (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hs).resolve_right
              (by rwa [IsUnit.neg_iff])
      obtain ⟨h, hh, hcl, -⟩ := exists_mul_columnsCleared_succ H (fun _ => True) hk g' hg'cl
        hg'u.unit rfl (fun i hi => htr hi _) (fun _ _ _ _ => trivial) trivial
      apply hg'H
      simpa using H.mul_mem (H.inv_mem hh) (ih (k + 1) (by omega) _ hcl)
  exact main (n - 0) 0 rfl g fun j hj => absurd hj (Nat.not_lt_zero _)

/-- **Generation of the Iwahori subgroup.** Over a local ring, a subgroup containing the
invertible diagonal matrices, the transvections `1 + c E_{ij}` with `i < j`, and those with
`i > j` and `c` in the maximal ideal contains every invertible matrix whose entries below the
diagonal lie in the maximal ideal. -/
theorem mem_of_iwahori (hdiag : ∀ d : Fin n → Rˣ, diagUnit d ∈ H)
    (hup : ∀ {i j : Fin n} (hij : i < j) (c : R), transvectionUnit hij.ne c ∈ H)
    (hlow : ∀ {i j : Fin n} (hij : j < i) (c : R), c ∈ IsLocalRing.maximalIdeal R →
      transvectionUnit hij.ne' c ∈ H)
    (g : GL (Fin n) R)
    (hg : ∀ i j : Fin n, j < i → (g : Matrix (Fin n) (Fin n) R) i j ∈
      IsLocalRing.maximalIdeal R) : g ∈ H := by
  let Inv : GL (Fin n) R → Prop := fun M => ∀ i j : Fin n, j < i →
    (M : Matrix (Fin n) (Fin n) R) i j ∈ IsLocalRing.maximalIdeal R
  have main : ∀ m k, n - k = m → ∀ g : GL (Fin n) R, Inv g →
      ColumnsCleared (g : Matrix (Fin n) (Fin n) R) k → g ∈ H := by
    intro m
    induction m with
    | zero =>
      intro k hk g _ hg
      exact mem_of_columnsCleared_all H hdiag g fun j hj => hg j (by omega)
    | succ m ih =>
      intro k hkm g hgI hg
      have hk : k < n := by omega
      set kk : Fin n := ⟨k, hk⟩
      obtain ⟨i₀, hi₀k, hi₀⟩ := exists_isUnit_of_columnsCleared g hg hk
      have hi₀eq : i₀ = kk := by
        by_contra hne
        have hlt : kk < i₀ := by
          rw [Fin.lt_def]
          exact lt_of_le_of_ne hi₀k (fun h => hne (Fin.ext h.symm))
        exact (IsLocalRing.mem_maximalIdeal _).1 (hgI i₀ kk hlt) hi₀
      rw [hi₀eq] at hi₀
      have hInv : ∀ M : GL (Fin n) R, Inv M → ∀ i (hi : i ≠ kk),
          Inv (transvectionUnit hi (-(g : Matrix (Fin n) (Fin n) R) i kk * ↑(hi₀.unit)⁻¹) * M) := by
        intro M hM i hi p q hqp
        rw [transvectionUnit_mul_apply]
        split_ifs with hp
        · subst hp
          refine Ideal.add_mem _ (hM p q hqp) ?_
          rcases lt_or_gt_of_ne hi with hlt | hgt
          · exact Ideal.mul_mem_left _ _ (hM kk q (lt_trans hqp hlt))
          · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
              ((Ideal.neg_mem_iff _).2 (hgI p kk hgt)))
        · exact hM p q hqp
      have hT : ∀ i (hi : i ≠ kk),
          transvectionUnit hi (-(g : Matrix (Fin n) (Fin n) R) i kk * ↑(hi₀.unit)⁻¹) ∈ H := by
        intro i hi
        rcases lt_or_gt_of_ne hi with hlt | hgt
        · exact hup hlt _
        · exact hlow hgt _ (Ideal.mul_mem_right _ _ ((Ideal.neg_mem_iff _).2 (hgI i kk hgt)))
      obtain ⟨h, hh, hcl, hinv⟩ := exists_mul_columnsCleared_succ H Inv hk g hg hi₀.unit rfl
        hT hInv hgI
      simpa using H.mul_mem (H.inv_mem hh) (ih (k + 1) (by omega) _ hinv hcl)
  exact main (n - 0) 0 rfl g hg fun j hj => absurd hj (Nat.not_lt_zero _)

end Langlands.Geometry.Building.GeneralLinearParahoric
