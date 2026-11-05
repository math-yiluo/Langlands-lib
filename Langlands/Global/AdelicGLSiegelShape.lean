import Langlands.Global.AdelicGLStandardCompact
import Langlands.Global.PrimitiveAdelicUnipotent
import Langlands.Global.NormOneIdeleClassCompact

/-! # Siegel sets for the actual adelic `GL(n)` -/

noncomputable section

universe u

open scoped Matrix NNReal

namespace Langlands.Global.PrimitiveAdelicHeight

/-! ## Triangular and diagonal matrices -/

section Triangular

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The diagonal of a product of upper triangular matrices is the product of the diagonals. -/
theorem diag_mul_of_isUpperTriangular {A B : Matrix (Fin n) (Fin n) R}
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hk | hk
    · rw [hA hk, zero_mul]
    · rw [hB hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The inverse of an upper triangular invertible matrix is upper triangular. -/
theorem isUpperTriangular_inv {g : Matrix.GeneralLinearGroup (Fin n) R}
    (hg : g.val.IsUpperTriangular) : (g⁻¹).val.IsUpperTriangular := by
  let := g.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hg

theorem inv_diag_mul_diag {g : Matrix.GeneralLinearGroup (Fin n) R}
    (hg : g.val.IsUpperTriangular) (i : Fin n) : (g⁻¹).val i i * g.val i i = 1 := by
  rw [← diag_mul_of_isUpperTriangular (isUpperTriangular_inv hg) hg, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]

/-- A diagonal entry of an upper triangular invertible matrix, as a unit. -/
def diagonalUnit (g : Matrix.GeneralLinearGroup (Fin n) R) (hg : g.val.IsUpperTriangular)
    (i : Fin n) : Rˣ where
  val := g.val i i
  inv := (g⁻¹).val i i
  val_inv := by rw [mul_comm]; exact inv_diag_mul_diag hg i
  inv_val := inv_diag_mul_diag hg i

/-- The invertible diagonal matrix with the given unit diagonal entries. -/
def diagonalGL (d : Fin n → Rˣ) : Matrix.GeneralLinearGroup (Fin n) R where
  val := Matrix.diagonal fun i => (d i : R)
  inv := Matrix.diagonal fun i => ((d i)⁻¹ : Rˣ)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp

theorem map_diagonalGL {S : Type*} [CommRing S] (f : R →+* S) (d : Fin n → Rˣ) :
    (Matrix.GeneralLinearGroup.map f (diagonalGL d)).val =
      Matrix.diagonal fun i => f (d i : R) := by
  change (Matrix.diagonal fun i => (d i : R)).map f = _
  rw [Matrix.diagonal_map (map_zero f)]

/-- An upper triangular matrix whose diagonal is `s`, multiplied on the right by the
diagonal matrix of the inverses of `s`, is unitriangular. -/
theorem isUnitriangular_mul_diagonal {P : Matrix (Fin n) (Fin n) R}
    (hP : P.IsUpperTriangular) (s : Fin n → Rˣ) (hs : ∀ i, P i i = s i) :
    IsUnitriangular (P * Matrix.diagonal fun i => (((s i)⁻¹ : Rˣ) : R)) :=
  ⟨Matrix.BlockTriangular.mul hP (Matrix.blockTriangular_diagonal _), fun i => by
    rw [Matrix.mul_diagonal, hs i, Units.mul_inv]⟩

/-- Conjugation by an invertible diagonal matrix preserves unitriangularity. -/
theorem IsUnitriangular.diagonal_conj {N : Matrix (Fin n) (Fin n) R}
    (hN : IsUnitriangular N) (d : Fin n → Rˣ) :
    IsUnitriangular (Matrix.diagonal (fun i => (d i : R)) * N *
      Matrix.diagonal fun i => (((d i)⁻¹ : Rˣ) : R)) := by
  refine ⟨Matrix.BlockTriangular.mul
    (Matrix.BlockTriangular.mul (Matrix.blockTriangular_diagonal _) hN.1)
    (Matrix.blockTriangular_diagonal _), fun i => ?_⟩
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hN.2 i, mul_one, Units.mul_inv]

end Triangular

/-- An elementary comparison of ratios used for the chamber condition. -/
theorem chamber_le {Si Sj Ti Tj Ui Uj c m M : ℝ} (hm : 0 < m) (hTi : 0 < Ti) (hTj : 0 < Tj)
    (hUi0 : 0 ≤ Ui) (hM : 0 ≤ M) (hi : Si * Ti = Ui) (hj : Sj * Tj = Uj) (hT : Ti ≤ c * Tj)
    (hUi : m ≤ Ui) (hUj : Uj ≤ M) : Sj ≤ c * M / m * Si := by
  have hSi : Si = Ui / Ti := by rw [← hi, mul_div_cancel_right₀ _ hTi.ne']
  have hSj : Sj = Uj / Tj := by rw [← hj, mul_div_cancel_right₀ _ hTj.ne']
  rw [hSi, hSj, div_mul_div_comm, div_le_div_iff₀ hTj (mul_pos hm hTi)]
  calc Uj * (m * Ti) ≤ M * (Ui * (c * Tj)) :=
        mul_le_mul hUj (mul_le_mul hUi hT hTi.le hUi0) (by positivity) hM
    _ = c * M * Ui * Tj := by ring

variable (F : Type u) [Field F] [NumberField F]

/-- An idele that is `1` at every finite place and whose infinite components have norms in
`[m, M]` has normalized absolute value in `[m ^ d, M ^ d]`, `d = [F : ℚ]`. -/
theorem full_bounds_of_local {x : Ideles F} {m M : ℝ} (hm : 0 ≤ m)
    (hfin : ∀ v, x.val.2 v = 1) (hinf : ∀ w, m ≤ ‖x.val.1 w‖ ∧ ‖x.val.1 w‖ ≤ M) :
    m ^ Module.finrank ℚ F ≤ ((IdeleAbsoluteValue.full F x : ℝ≥0) : ℝ) ∧
      ((IdeleAbsoluteValue.full F x : ℝ≥0) : ℝ) ≤ M ^ Module.finrank ℚ F := by
  have hf : ∏ᶠ v, ‖x.val.2 v‖ = 1 := by
    simp only [hfin, norm_one, finprod_one]
  rw [IdeleAbsoluteValue.coe_full, hf, mul_one, ← NumberField.InfinitePlace.sum_mult_eq,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
  constructor
  · exact Finset.prod_le_prod₀ (fun w _ => pow_nonneg hm _)
      (fun w _ => pow_le_pow_left₀ hm (hinf w).1 _)
  · exact Finset.prod_le_prod₀ (fun w _ => pow_nonneg (norm_nonneg _) _)
      (fun w _ => pow_le_pow_left₀ (norm_nonneg _) (hinf w).2 _)

/-! ## The Siegel set -/

variable (n : ℕ)

/-- The `GL(n)` Siegel set `Ω_N · Ω_M · A(c) · K` in the actual adelic `GL(n)`: matrices
`N · diag(ω) · diag(a) · κ` with `N ∈ Ω_N`, every `ω i ∈ C`, `a i` the positive real idele
with value `r i` at every infinite place and `1` at every finite place, `κ` in the standard
compact subgroup, and `|a (i + 1)| ≤ c · |a i|` for the normalized idele absolute value. -/
def siegelSetGL (ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))) (C : Set (Ideles F)) (c : ℝ) :
    Set (AdelicGL F n) :=
  {h | ∃ (N : Matrix (Fin n) (Fin n) (Adeles F)) (ω : Fin n → Ideles F) (r : Fin n → ℝ≥0ˣ)
      (κ : AdelicGL F n),
      h.val = N * Matrix.diagonal (fun i => (ω i).val) *
          Matrix.diagonal (fun i => (PositiveRealIdeles.full F (r i)).val) * κ.val ∧
        N ∈ ΩN ∧ (∀ i, ω i ∈ C) ∧ κ ∈ standardCompact F n ∧
        ∀ i j : Fin n, i.val + 1 = j.val →
          ((IdeleAbsoluteValue.full F (PositiveRealIdeles.full F (r j)) : ℝ≥0) : ℝ) ≤
            c * ((IdeleAbsoluteValue.full F (PositiveRealIdeles.full F (r i)) : ℝ≥0) : ℝ)}

/-- **Siegel sets for `GL(n)`.** There are a compact set `Ω_N` of unitriangular adelic
matrices, a compact set `C` of norm-one ideles and a constant `c > 0` such that every
actual adelic invertible matrix becomes an element of `siegelSetGL F n Ω_N C c` after left
multiplication by a rational invertible matrix. -/
theorem exists_rational_mul_mem_siegelSetGL :
    ∃ (ΩN : Set (Matrix (Fin n) (Fin n) (Adeles F))) (C : Set (Ideles F)) (c : ℝ),
      IsCompact ΩN ∧ (∀ N ∈ ΩN, IsUnitriangular N) ∧ IsCompact C ∧
        C ⊆ NormOneIdeleClass.normOneIdeles F ∧ 0 < c ∧
        ∀ g : AdelicGL F n, ∃ γ : RationalGL F n,
          AdelicGL.rational F n γ * g ∈ siegelSetGL F n ΩN C c := by
  classical
  obtain ⟨c, B, hc, hB, hred⟩ := exists_reduction_GL F n
  obtain ⟨Ω, hΩ, hΩN, hΩred⟩ := exists_isCompact_unitriangular_reduction F n
  obtain ⟨C, hC, hC1, hCfs⟩ := NormOneIdeleClass.exists_isCompact_fundamentalSet F
  let d := Module.finrank ℚ F
  let m : ℝ := (Real.sqrt n * B)⁻¹
  let M : ℝ := (Real.sqrt n * B) ^ n
  let A : Ideles F → ℝ := fun x => ((IdeleAbsoluteValue.full F x : ℝ≥0) : ℝ)
  have hA_mul : ∀ x y, A (x * y) = A x * A y := fun x y => by
    simp only [A, map_mul, Units.val_mul, NNReal.coe_mul]
  have hA_pos : ∀ x, 0 < A x := fun x =>
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hM : 0 ≤ M := pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) (zero_le_one.trans hB)) _
  refine ⟨Ω, C, max 1 (c * M ^ d / m ^ d), hΩ, hΩN, hC, hC1,
    zero_lt_one.trans_le (le_max_left _ _), fun g => ?_⟩
  obtain ⟨γ, k, b, hg, hk, hbU, t, hbt, ht⟩ := hred g⁻¹
  obtain ⟨β, κ, hkβ, hκ, hβ, hβfin, hβbd⟩ :=
    exists_upperTriangular_mul_mem_standardCompact F n hB hk
  -- the triangular factor `p = b⁻¹ β`
  let p := b⁻¹ * β
  have hp : p.val.IsUpperTriangular := Matrix.BlockTriangular.mul (isUpperTriangular_inv hbU) hβ
  have hpg : AdelicGL.rational F n γ⁻¹ * g = p * κ := by
    calc AdelicGL.rational F n γ⁻¹ * g = (g⁻¹ * AdelicGL.rational F n γ)⁻¹ := by
          rw [mul_inv_rev, inv_inv, map_inv]
      _ = (k * b)⁻¹ := by rw [hg]
      _ = b⁻¹ * k⁻¹ := mul_inv_rev k b
      _ = p * κ := by
          show b⁻¹ * k⁻¹ = b⁻¹ * β * κ
          rw [hkβ, ← mul_assoc]
  -- the diagonal of `p`
  let u : Fin n → Ideles F := diagonalUnit β hβ
  let s : Fin n → Ideles F := fun i => (t i)⁻¹ * u i
  have hbinv : ∀ i, (b⁻¹).val i i = ((t i)⁻¹ : Ideles F).val := fun i => by
    refine (Units.inv_eq_of_mul_eq_one_left ?_).symm
    rw [← hbt i]
    exact inv_diag_mul_diag hbU i
  have hps : ∀ i, p.val i i = (s i).val := fun i => by
    change (b⁻¹ * β).val i i = ((t i)⁻¹ * u i).val
    rw [Units.val_mul, Units.val_mul,
      diag_mul_of_isUpperTriangular (isUpperTriangular_inv hbU) hβ, hbinv]
    rfl
  have hts : ∀ i, A (s i) * A (t i) = A (u i) := fun i => by
    change A ((t i)⁻¹ * u i) * A (t i) = A (u i)
    rw [← hA_mul, mul_comm, mul_inv_cancel_left]
  -- bounds on the diagonal of `β`
  have hu : ∀ i, m ^ d ≤ A (u i) ∧ A (u i) ≤ M ^ d := fun i => by
    have h2 : (β.val i i).2 = 1 := by
      have h := congrArg (fun h : FiniteAdelicGL F n => h.val i i) hβfin
      rw [Units.val_one, Matrix.one_apply_eq] at h
      exact h
    refine full_bounds_of_local F (inv_nonneg.mpr (mul_nonneg (Real.sqrt_nonneg _)
      (zero_le_one.trans hB))) (fun v => ?_) (fun w => hβbd w i)
    change (β.val i i).2 v = 1
    rw [h2]
    rfl
  -- the positive real and norm-one parts of the diagonal
  let r : Fin n → ℝ≥0ˣ := fun i => scalarRoot F (IdeleAbsoluteValue.full F (s i))
  let a : Fin n → Ideles F := fun i => PositiveRealIdeles.full F (r i)
  have ha : ∀ i, IdeleAbsoluteValue.full F (a i) = IdeleAbsoluteValue.full F (s i) :=
    fun i => absoluteValue_scalarRoot F _
  have hnorm : ∀ i, s i * (a i)⁻¹ ∈ NormOneIdeleClass.normOneIdeles F := fun i => by
    rw [MonoidHom.mem_ker]
    change IdeleAbsoluteValue.full F (s i * (a i)⁻¹) = 1
    rw [map_mul, map_inv, ha, mul_inv_cancel]
  choose f hf using fun i => hCfs (s i * (a i)⁻¹) (hnorm i)
  let ω : Fin n → Ideles F := fun i => diagonalUnits F (f i) * (s i * (a i)⁻¹)
  have hs : ∀ i, s i = (diagonalUnits F (f i))⁻¹ * ω i * a i := fun i => by
    simp only [ω]
    rw [mul_assoc, mul_assoc, inv_mul_cancel_right, inv_mul_cancel_left]
  -- the unipotent part
  let N' := p.val * Matrix.diagonal fun i => ((s i)⁻¹ : Ideles F).val
  have hN' : IsUnitriangular N' := isUnitriangular_mul_diagonal hp s hps
  have hpN : p.val = N' * Matrix.diagonal fun i => (s i).val := by
    simp only [N']
    rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    simp
  let D : Fin n → Ideles F := fun i => diagonalUnits F (f i)
  let N'' := Matrix.diagonal (fun i => (D i).val) * N' *
    Matrix.diagonal fun i => ((D i)⁻¹ : Ideles F).val
  have hN'' : IsUnitriangular N'' := hN'.diagonal_conj D
  obtain ⟨μ, hμ, hμΩ⟩ := hΩred N'' hN''
  let μGL : RationalGL F n := Matrix.GeneralLinearGroup.mkOfDetNeZero μ
    (by rw [hμ.det_eq_one]; exact one_ne_zero)
  refine ⟨μGL * diagonalGL f * γ⁻¹, ?_⟩
  rw [siegelSetGL, Set.mem_ofPred_eq]
  refine ⟨μ.map (algebraMap F (Adeles F)) * N'', ω, r, κ, ?_, hμΩ, hf, hκ, ?_⟩
  · have hμval : (AdelicGL.rational F n μGL).val = μ.map (algebraMap F (Adeles F)) := rfl
    have hfval : (AdelicGL.rational F n (diagonalGL f)).val =
        Matrix.diagonal fun i => (D i).val := map_diagonalGL _ f
    have hsval : (Matrix.diagonal fun i => (s i).val) =
        (Matrix.diagonal fun i => ((D i)⁻¹ : Ideles F).val) *
          Matrix.diagonal (fun i => (ω i).val) * Matrix.diagonal fun i => (a i).val := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      rw [hs i, Units.val_mul, Units.val_mul]
    rw [map_mul, map_mul, mul_assoc, hpg]
    simp only [Units.val_mul]
    rw [hμval, hfval, hpN, hsval]
    simp only [N'', Matrix.mul_assoc]
    rfl
  · intro i j hij
    have hmpos : 0 < m := inv_pos.mpr (mul_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr i.pos))
      (zero_lt_one.trans_le hB))
    have hle := chamber_le (pow_pos hmpos d) (hA_pos (t i)) (hA_pos (t j)) (hA_pos (u i)).le
      (pow_nonneg hM d) (hts i) (hts j) (ht i j hij) (hu i).1 (hu j).2
    change A (a j) ≤ max 1 (c * M ^ d / m ^ d) * A (a i)
    have haj : A (a j) = A (s j) := congrArg (fun z : ℝ≥0ˣ => ((z : ℝ≥0) : ℝ)) (ha j)
    have hai : A (a i) = A (s i) := congrArg (fun z : ℝ≥0ˣ => ((z : ℝ≥0) : ℝ)) (ha i)
    rw [haj, hai]
    exact hle.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hA_pos (s i)).le)

end Langlands.Global.PrimitiveAdelicHeight
