import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.PowerSeries.Order

/-! # Detecting specialization with finitely many matrix coefficients -/

noncomputable section

open Matrix

namespace Langlands.Global.EisensteinJet

variable {R ι : Type*} [CommRing R] [IsDomain R] [Fintype ι] [DecidableEq ι]

/-- The number of coefficients needed for detection by a matrix with nonzero determinant. -/
def coefficientCount (A : Matrix ι ι (PowerSeries R)) : ℕ :=
  A.det.order.toNat + 1

/-- If the determinant is nonzero, the first `coefficientCount A` coefficients
of `A *ᵥ x` detect the constant coefficient of `x`. -/
theorem constantCoeff_eq_zero_of_mulVec (A : Matrix ι ι (PowerSeries R))
    (hA : A.det ≠ 0) (x : ι → PowerSeries R)
    (h : ∀ j (k : Fin (coefficientCount A)), PowerSeries.coeff (k : ℕ) ((A *ᵥ x) j) = 0) :
    ∀ i, PowerSeries.constantCoeff (x i) = 0 := by
  have hdvd : ∀ j, PowerSeries.X ^ coefficientCount A ∣ (A *ᵥ x) j := fun j =>
    PowerSeries.X_pow_dvd_iff.mpr fun k hk => h j ⟨k, hk⟩
  have hadj : A.adjugate *ᵥ (A *ᵥ x) = A.det • x := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  intro i
  have hprod : PowerSeries.X ^ coefficientCount A ∣ A.det * x i := by
    change PowerSeries.X ^ coefficientCount A ∣ (A.det • x) i
    rw [← hadj]
    change PowerSeries.X ^ coefficientCount A ∣ ∑ j, A.adjugate i j * (A *ᵥ x) j
    exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (hdvd j) _
  by_contra hi
  have hx : (x i).order = 0 := by
    refine le_antisymm (PowerSeries.order_le 0 ?_) bot_le
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have horder := PowerSeries.nat_le_order _ _ (PowerSeries.X_pow_dvd_iff.mp hprod)
  rw [PowerSeries.order_mul, hx, add_zero, ← PowerSeries.coe_toNat_order hA] at horder
  exact Nat.not_succ_le_self _ (ENat.natCast_le_natCast.mp horder)

end Langlands.Global.EisensteinJet
