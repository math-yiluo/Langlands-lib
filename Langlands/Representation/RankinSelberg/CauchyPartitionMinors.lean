import Langlands.Representation.RankinSelberg.PowerSeriesMinorCoefficients
import Mathlib.Order.Fin.Basic

/-! # Partitions and the minors of the Cauchy determinant -/

noncomputable section

namespace Langlands.GeneralLinear.Spherical

/-- Reverse the exponent tuple and remove the staircase. -/
def exponentPartition {n : ℕ} (e : Fin (n + 1) → ℕ) : Fin (n + 1) → ℤ :=
  fun i => (e i.rev : ℤ) - i.rev.val

/-- Add the staircase to a partition and reverse its coordinates. -/
def partitionExponents {n : ℕ} (α : Fin (n + 1) → ℤ) : Fin (n + 1) → ℕ :=
  fun i => (α i.rev + i.val).toNat

theorem le_strictMono_fin {n : ℕ} (e : Fin (n + 1) → ℕ) (he : StrictMono e)
    (i : Fin (n + 1)) : i.val ≤ e i := by
  refine Fin.induction (Nat.zero_le _) (fun j hj => ?_) i
  have h := he (show j.castSucc < j.succ from Fin.castSucc_lt_succ)
  simp only [Fin.val_succ]
  exact Nat.succ_le_of_lt (lt_of_le_of_lt hj h)

theorem exponentPartition_nonneg {n : ℕ} (e : Fin (n + 1) → ℕ) (he : StrictMono e) :
    ∀ i, 0 ≤ exponentPartition e i := by
  intro i
  have h := le_strictMono_fin e he i.rev
  unfold exponentPartition
  omega

theorem exponentPartition_antitone {n : ℕ} (e : Fin (n + 1) → ℕ) (he : StrictMono e) :
    Antitone (exponentPartition e) := by
  rw [Fin.antitone_iff_succ_le]
  intro i
  have h := he (Fin.rev_lt_rev.mpr (show i.castSucc < i.succ from Fin.castSucc_lt_succ))
  have h₁ := i.castSucc.add_rev_cast
  have h₂ := i.succ.add_rev_cast
  simp only [exponentPartition]
  simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂
  omega

theorem partitionExponents_strictMono {n : ℕ} (α : Fin (n + 1) → ℤ)
    (hα : Antitone α) (hpos : ∀ i, 0 ≤ α i) : StrictMono (partitionExponents α) := by
  intro i j hij
  have h := hα (Fin.rev_le_rev.mpr hij.le)
  have hi := hpos i.rev
  have hj := hpos j.rev
  have hij' : i.val < j.val := hij
  unfold partitionExponents
  omega

theorem partitionExponents_exponentPartition {n : ℕ} (e : Fin (n + 1) → ℕ) :
    partitionExponents (exponentPartition e) = e := by
  funext i
  simp [partitionExponents, exponentPartition]

theorem exponentPartition_partitionExponents {n : ℕ} (α : Fin (n + 1) → ℤ)
    (hpos : ∀ i, 0 ≤ α i) : exponentPartition (partitionExponents α) = α := by
  funext i
  simp only [exponentPartition, partitionExponents, Fin.rev_rev]
  have h := hpos i
  rw [Int.toNat_of_nonneg (by omega)]
  omega

/-- Increasing natural exponents are equivalent to nonnegative antitone integral weights. -/
def partitionExponentEquiv (n : ℕ) :
    {e : Fin (n + 1) → ℕ // StrictMono e} ≃
      {α : Fin (n + 1) → ℤ // Antitone α ∧ ∀ i, 0 ≤ α i} where
  toFun e := ⟨exponentPartition e.val, exponentPartition_antitone e.val e.property,
    exponentPartition_nonneg e.val e.property⟩
  invFun α := ⟨partitionExponents α.val,
    partitionExponents_strictMono α.val α.property.1 α.property.2⟩
  left_inv e := Subtype.ext (partitionExponents_exponentPartition e.val)
  right_inv α := Subtype.ext (exponentPartition_partitionExponents α.val α.property.2)

theorem sum_exponentPartition {n : ℕ} (e : Fin (n + 1) → ℕ) :
    ((∑ i, e i : ℕ) : ℤ) =
      (∑ i, exponentPartition e i) + ((∑ i : Fin (n + 1), i.rev.val : ℕ) : ℤ) := by
  have hrev : (∑ i : Fin (n + 1), (e i.rev : ℤ)) = ∑ i : Fin (n + 1), (e i : ℤ) :=
    by simpa only [Fin.revPerm_apply] using
      (Equiv.sum_comp Fin.revPerm (fun i : Fin (n + 1) => (e i : ℤ)))
  simp only [exponentPartition, Finset.sum_sub_distrib]
  push_cast
  rw [hrev]
  ring

variable {R : Type*} [CommRing R]

/-- Jacobi–Trudi for the coefficients of an arbitrary formal power series. -/
def seriesJacobiTrudi {m : ℕ} (H : PowerSeries R) (α : Fin m → ℤ) : R :=
  Matrix.det (Matrix.of fun i j : Fin m => seriesCoeff H (α i - i + j))

/-- Monomials with the exponents belonging to a weight and its staircase. -/
def weightMonomialMatrix {n : ℕ} (y : Fin (n + 1) → R) (α : Fin (n + 1) → ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j => y j ^ (α i - i + n).toNat

/-- Reversing coefficient-minor columns and transposing gives Jacobi–Trudi. -/
theorem seriesCoefficientMinor_reverse_transpose {n : ℕ}
    (H : PowerSeries R) (e : Fin (n + 1) → ℕ) :
    ((seriesCoefficientMinor H e).submatrix id Fin.revPerm).transpose =
      Matrix.of (fun i j : Fin (n + 1) =>
        seriesCoeff H (exponentPartition e i - i + j)) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id_eq,
    seriesCoefficientMinor, Matrix.of_apply, Fin.revPerm_apply, exponentPartition]
  congr 1
  have hi := i.add_rev_cast
  have hj := j.add_rev_cast
  omega

theorem monomialMinor_reverse {n : ℕ} (y : Fin (n + 1) → R) (e : Fin (n + 1) → ℕ) :
    (monomialMinor y e).submatrix Fin.revPerm id =
      weightMonomialMatrix y (exponentPartition e) := by
  apply Matrix.ext
  intro i j
  simp only [monomialMinor, weightMonomialMatrix, Matrix.submatrix_apply,
    Matrix.of_apply, id_eq, Fin.revPerm_apply, exponentPartition]
  congr 1
  have hi := i.add_rev_cast
  omega

/-- A Cauchy–Binet minor pair is the Jacobi–Trudi/alternant pair of its partition. -/
theorem minor_product_eq_partition {n : ℕ} (H : PowerSeries R)
    (y : Fin (n + 1) → R) (e : Fin (n + 1) → ℕ) :
    Matrix.det (seriesCoefficientMinor H e) * Matrix.det (monomialMinor y e) =
      seriesJacobiTrudi H (exponentPartition e) *
        Matrix.det (weightMonomialMatrix y (exponentPartition e)) := by
  rw [← det_minor_product_permute (seriesCoefficientMinor H e) (monomialMinor y e) Fin.revPerm,
    ← Matrix.det_transpose ((seriesCoefficientMinor H e).submatrix id Fin.revPerm),
    seriesCoefficientMinor_reverse_transpose, monomialMinor_reverse]
  rfl

end Langlands.GeneralLinear.Spherical
