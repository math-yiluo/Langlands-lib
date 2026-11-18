import Langlands.Representation.Plancherel.LaurentUnitaryBoundedCancellation

/-! # Cancellation of unitary coordinate pole multiplicities -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace Langlands.Plancherel

universe uX uW

/-- Continuous norm inequalities valid on a dense subset hold everywhere. -/
theorem norm_le_of_dense
    {X : Type uX} [TopologicalSpace X]
    {W : Type uW} [SeminormedAddCommGroup W]
    (f : X → W) (g : X → ℂ) (hf : Continuous f) (hg : Continuous g)
    (D : Set X) (hD : Dense D) (c : ℝ)
    (hbound : ∀ z ∈ D, ‖f z‖ ≤ c * ‖g z‖) :
    ∀ z, ‖f z‖ ≤ c * ‖g z‖ := by
  have hclosed : IsClosed {w | ‖f w‖ ≤ c * ‖g w‖} :=
    isClosed_le hf.norm (continuous_const.mul hg.norm)
  exact fun z => closure_minimal hbound hclosed (hD z)

/-- Every nonzero finite Laurent polynomial has dense nonvanishing locus on
the entire unitary torus. -/
theorem finiteLaurent_unitary_dense_nonzero {n : ℕ}
    (p : AddMonoidAlgebra ℂ (Fin n → ℤ)) (hp : p ≠ 0) :
    Dense {z : Fin n → Circle |
      finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) p ≠ 0} := by
  rw [dense_iff_inter_open]
  intro U hU hne
  by_contra h
  apply hp
  apply finiteLaurent_eq_zero_of_eval_unitary_open p hU hne
  intro z hz
  by_contra hnz
  exact h ⟨z, hz, hnz⟩

/-- Evaluation of the coordinate root has the displayed root and sign. -/
theorem finiteLaurentCoordinateRoot_eval_cons (n : ℕ) (a d : ℂˣ)
    (z : Fin n → ℂˣ) :
    finiteLaurentEvaluation (Fin.cons d z) (finiteLaurentCoordinateRoot n a) =
      (d : ℂ) - (a : ℂ) := by
  rw [finiteLaurentEvaluation_cons, finiteLaurentCoordinateRoot,
    RingEquiv.apply_symm_apply, map_sub, LaurentPolynomial.eval₂_T,
    LaurentPolynomial.eval₂_C]
  simp only [zpow_one]
  exact congrArg (fun t : ℂ => (d : ℂ) - t) ((finiteLaurentEvaluation z).commutes (a : ℂ))

/-- A circle coordinate root is a nonzero Laurent polynomial. -/
theorem finiteLaurentCoordinateRoot_ne_zero (n : ℕ) (a : Circle) :
    finiteLaurentCoordinateRoot n (Circle.toUnits a) ≠ 0 := by
  intro h
  have he := congrArg
    (finiteLaurentEvaluation (Fin.cons (Circle.toUnits (-a)) (fun _ : Fin n => 1))) h
  rw [finiteLaurentCoordinateRoot_eval_cons, map_zero] at he
  exact Circle.neg_ne_self a (Circle.coe_injective (sub_eq_zero.mp he))

/-- Removing a common nonzero Laurent factor preserves the same norm bound.
The nonzero locus is dense on the unitary torus, so no bound at a quotient's
singular points is assumed. -/
theorem finiteLaurent_unitary_bound_cancel_factor
    {n : ℕ} (r p b : AddMonoidAlgebra ℂ (Fin n → ℤ)) (hr : r ≠ 0) (c : ℝ)
    (hbound : ∀ z : Fin n → Circle,
      ‖finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) (r * p)‖ ≤
        c * ‖finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) (r * b)‖) :
    ∀ z : Fin n → Circle,
      ‖finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) p‖ ≤
        c * ‖finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) b‖ := by
  apply norm_le_of_dense
    (fun z : Fin n → Circle =>
      finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) p)
    (fun z : Fin n → Circle =>
      finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) b)
    (continuous_finiteLaurentEvaluation_circle p)
    (continuous_finiteLaurentEvaluation_circle b)
    _ (finiteLaurent_unitary_dense_nonzero r hr) c
  intro z hz
  have hi := hbound z
  simp only [map_mul, norm_mul] at hi
  apply (mul_le_mul_iff_right₀ (norm_pos_iff.mpr hz)).mp
  simpa only [mul_assoc, mul_left_comm] using hi

/-- Every prescribed power of a unit-circle coordinate root in the denominator
also divides a Laurent numerator with the stated dense unitary bound. The
power is chosen from the denominator before the numerator is considered. -/
theorem finiteLaurentCoordinateRoot_pow_dvd_of_dense_unitary_bound
    {n : ℕ} (a : Circle) (k : ℕ)
    (p b : AddMonoidAlgebra ℂ (Fin (n + 1) → ℤ))
    (D : Set (Fin (n + 1) → Circle)) (hD : Dense D) (c : ℝ)
    (hbound : ∀ z ∈ D,
      ‖finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) p‖ ≤
        c * ‖finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) b‖)
    (hb : finiteLaurentCoordinateRoot n (Circle.toUnits a) ^ k ∣ b) :
    finiteLaurentCoordinateRoot n (Circle.toUnits a) ^ k ∣ p := by
  have hglobal := norm_le_of_dense
    (fun z : Fin (n + 1) → Circle =>
      finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) p)
    (fun z : Fin (n + 1) → Circle =>
      finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) b)
    (continuous_finiteLaurentEvaluation_circle p)
    (continuous_finiteLaurentEvaluation_circle b) D hD c hbound
  clear hbound hD D
  induction k generalizing p b with
  | zero => simp
  | succ k ih =>
      let r := finiteLaurentCoordinateRoot n (Circle.toUnits a)
      obtain ⟨b₂, hb₂⟩ := hb
      have hb' : b = r * (r ^ k * b₂) := by
        simpa only [r, pow_succ', mul_assoc] using hb₂
      have hrb : r ∣ b := ⟨r ^ k * b₂, hb'⟩
      have hrp := finiteLaurentCoordinateRoot_dvd_of_dense_unitary_bound
        a p b Set.univ dense_univ c (fun z hz => hglobal z) hrb
      obtain ⟨p₁, hp₁⟩ := hrp
      have hquot :
          ∀ z : Fin (n + 1) → Circle,
            ‖finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) p₁‖ ≤
              c * ‖finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) (r ^ k * b₂)‖ :=
        finiteLaurent_unitary_bound_cancel_factor r p₁ (r ^ k * b₂)
          (finiteLaurentCoordinateRoot_ne_zero n a) c (by
            intro z
            simpa only [hp₁, hb'] using hglobal z)
      have hpow : r ^ k ∣ p₁ :=
        ih p₁ (r ^ k * b₂) (dvd_mul_right _ _) hquot
      simpa only [r, pow_succ', hp₁] using mul_dvd_mul_left r hpow

section Quotient

variable {n : ℕ} (a : Circle) (k : ℕ)
  (p b : AddMonoidAlgebra ℂ (Fin (n + 1) → ℤ))
  (D : Set (Fin (n + 1) → Circle)) (hD : Dense D) (c : ℝ)
  (hbound : ∀ z ∈ D,
    ‖finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) p‖ ≤
      c * ‖finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) b‖)
  (hb : finiteLaurentCoordinateRoot n (Circle.toUnits a) ^ k ∣ b)

/-- The polynomial quotient after canceling the prescribed unitary coordinate
pole power, constructed from the proved dense-bound divisibility criterion. -/
def finiteLaurentCoordinatePowerQuotient :
    AddMonoidAlgebra ℂ (Fin (n + 1) → ℤ) :=
  Classical.choose
    (finiteLaurentCoordinateRoot_pow_dvd_of_dense_unitary_bound a k p b D hD c hbound hb)

/-- The constructed quotient satisfies its polynomial factor identity,
including at unitary points where the original denominator vanishes. -/
theorem finiteLaurentCoordinatePowerQuotient_spec :
    p = finiteLaurentCoordinateRoot n (Circle.toUnits a) ^ k *
      finiteLaurentCoordinatePowerQuotient a k p b D hD c hbound hb :=
  Classical.choose_spec
    (finiteLaurentCoordinateRoot_pow_dvd_of_dense_unitary_bound a k p b D hD c hbound hb)

end Quotient

end Langlands.Plancherel
