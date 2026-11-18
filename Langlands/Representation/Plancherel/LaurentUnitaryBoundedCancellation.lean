import Langlands.Representation.Plancherel.LaurentUnitaryHyperplaneDivisibility

/-! # Cancellation of coordinate poles from dense unitary bounds -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace Langlands.Plancherel

universe uX uW

/-- Restriction of finite Laurent polynomials to the unitary torus, as an
algebra homomorphism into the actual scalar function algebra. -/
def finiteLaurentUnitaryEvaluation (n : ℕ) :
    AddMonoidAlgebra ℂ (Fin n → ℤ) →ₐ[ℂ] ((Fin n → Circle) → ℂ) where
  toFun p z := finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) p
  map_zero' := funext fun _z => map_zero _
  map_one' := funext fun _z => map_one _
  map_add' p q := funext fun _z => map_add _ p q
  map_mul' p q := funext fun _z => map_mul _ p q
  commutes' c := funext fun z =>
    (finiteLaurentEvaluation (fun i => Circle.toUnits (z i))).commutes c

@[simp]
theorem finiteLaurentUnitaryEvaluation_apply {n : ℕ}
    (p : AddMonoidAlgebra ℂ (Fin n → ℤ)) (z : Fin n → Circle) :
    finiteLaurentUnitaryEvaluation n p z =
      finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) p := rfl

/-- Every function in the constructed unitary restriction algebra is
continuous on the entire unitary torus. -/
theorem continuous_finiteLaurentUnitaryEvaluation {n : ℕ}
    (p : AddMonoidAlgebra ℂ (Fin n → ℤ)) :
    Continuous (finiteLaurentUnitaryEvaluation n p) :=
  continuous_finiteLaurentEvaluation_circle p

/-- A continuous numerator bounded by a constant times a continuous scalar
denominator on a dense set vanishes at every zero of that denominator. -/
theorem norm_eq_zero_of_dense_norm_le
    {X : Type uX} [TopologicalSpace X]
    {W : Type uW} [SeminormedAddCommGroup W]
    (f : X → W) (g : X → ℂ) (hf : Continuous f) (hg : Continuous g)
    (D : Set X) (hD : Dense D) (c : ℝ)
    (hbound : ∀ z ∈ D, ‖f z‖ ≤ c * ‖g z‖)
    (z : X) (hgzero : g z = 0) :
    ‖f z‖ = 0 := by
  have hclosed : IsClosed {w | ‖f w‖ ≤ c * ‖g w‖} :=
    isClosed_le hf.norm (continuous_const.mul hg.norm)
  have hi : ‖f z‖ ≤ c * ‖g z‖ := closure_minimal hbound hclosed (hD z)
  rw [hgzero, norm_zero, mul_zero] at hi
  exact le_antisymm hi (norm_nonneg _)

/-- A coordinate root on the unit circle cancels from a Laurent numerator
whenever the ratio has a uniform bound on a dense unitary generic set.
The bound is supplied as a cleared numerator inequality, so no quotient value
at a pole or ambient-open extension is assumed. -/
theorem finiteLaurentCoordinateRoot_dvd_of_dense_unitary_bound
    {n : ℕ} (a : Circle)
    (p b : AddMonoidAlgebra ℂ (Fin (n + 1) → ℤ))
    (D : Set (Fin (n + 1) → Circle)) (hD : Dense D) (c : ℝ)
    (hbound : ∀ z ∈ D,
      ‖finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) p‖ ≤
        c * ‖finiteLaurentEvaluation (fun i => Circle.toUnits (z i)) b‖)
    (hb : finiteLaurentCoordinateRoot n (Circle.toUnits a) ∣ b) :
    finiteLaurentCoordinateRoot n (Circle.toUnits a) ∣ p := by
  have hbzero := (finiteLaurentCoordinateRoot_dvd_iff n (Circle.toUnits a) b).mp hb
  apply finiteLaurentCoordinateRoot_dvd_of_eval_unitary_open
    (n := n) (U := Set.univ) (Circle.toUnits a) p isOpen_univ Set.univ_nonempty
  intro z hz
  have hcoords :
      (fun i : Fin (n + 1) =>
        Circle.toUnits ((Fin.cons a z : Fin (n + 1) → Circle) i)) =
        Fin.cons (Circle.toUnits a) (fun i => Circle.toUnits (z i)) := by
    funext i
    exact Fin.cases rfl (fun j => rfl) i
  have hbz :
      finiteLaurentEvaluation (fun i =>
        Circle.toUnits ((Fin.cons a z : Fin (n + 1) → Circle) i)) b = 0 := by
    rw [hcoords, ← finiteLaurentEvaluation_firstEvaluation, hbzero, map_zero]
  have hpz := norm_eq_zero_of_dense_norm_le
    (fun w : Fin (n + 1) → Circle =>
      finiteLaurentEvaluation (fun i => Circle.toUnits (w i)) p)
    (fun w : Fin (n + 1) → Circle =>
      finiteLaurentEvaluation (fun i => Circle.toUnits (w i)) b)
    (continuous_finiteLaurentEvaluation_circle p)
    (continuous_finiteLaurentEvaluation_circle b) D hD c hbound
      (Fin.cons a z : Fin (n + 1) → Circle) hbz
  rw [hcoords] at hpz
  exact norm_eq_zero.mp hpz

end Langlands.Plancherel
