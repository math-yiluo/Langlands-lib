import Langlands.Representation.Archimedean.RealSphericalStep
import Langlands.Representation.Archimedean.JacquetNonvanishing

/-!
# The regularized spherical vector lies in the Lie span of the spherical vector

Let `χ` be signed-power characters with exponents `e` and trivial signs, and let `A` be a
subspace of the `O(m+1)`-finite functions of the principal series of `χ` on `GL_{m+1}(ℝ)` that is
stable under all right derivatives and contains the spherical vector `T₀` (equal to `1` on
`O(m+1)`). If `e_m - e_j - 1 ≠ 0` for all `j < m`, then `A` also contains the function `H` of the
principal series whose restriction to `O(m+1)` is `κ ↦ κ_{mm}²`.

The proof follows quadratic functions on `O(m+1)`: the set of `p ∈ ℂ^{m+1}` for which there are
`G_0, …, G_m ∈ A` with `G_c(κ) = ∑_l p_l κ_{lc} κ_{lm}` on `O(m+1)` is a subspace, contains the
all-ones vector (take `G_m = T₀`, `G_c = 0` otherwise) and is stable under the operator `S` of
`RealSphericalKrylov` (by the step formula of `RealSphericalStep`). Hence it contains the last
standard basis vector, and the corresponding `G_m` agrees with `H` on `O(m+1)`.
-/

noncomputable section

open scoped Manifold ContDiff Matrix Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option backward.isDefEq.respectTransparency false

namespace RealSphericalReach

open RealPrincipalSeriesDuality RealBlockDerivative RealSphericalKrylov RealSphericalStep
  PartialJacquet JacquetNonvanishing GramFormula

variable {N : ℕ} {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}

/-! ## Exponential equivariance -/

theorem apply_exp (hχ : IsSignedPower χ e) (l : ℕ) (x : ℝ) :
    χ l (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') = Complex.exp (e l * x) := by
  have hs : signUnit (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') = 1 := by
    unfold signUnit
    exact ite_eq_left_iff.mpr fun h => absurd (Real.exp_pos x) h
  rw [hχ.eq, hs, hχ.one, one_mul, Units.val_mk0, abs_of_pos (Real.exp_pos x),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, mul_comm]

/-- Elements of the principal series of `χ` are exponent-equivariant for
`α_i = e_i + (N - 1)/2 - i`. -/
theorem isExpEquivariant_of_mem (hχ : IsSignedPower χ e) {f : Langlands.GeneralLinear N ℝ → ℂ}
    (hf : f ∈ principalSeries ℝ N χ) :
    IsExpEquivariant (fun i : Fin N => e i + ((N : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) f :=
  isExpEquivariant_of_mem_principalSeries (τ := fun i => e i) (fun i x => apply_exp hχ i x) hf

/-! ## Quadratic functions -/

theorem quad_zero (c b : Fin N) (M : Matrix (Fin N) (Fin N) ℝ) : quad 0 c b M = 0 := by
  simp [quad]

theorem quad_add (p q : Fin N → ℂ) (c b : Fin N) (M : Matrix (Fin N) (Fin N) ℝ) :
    quad (p + q) c b M = quad p c b M + quad q c b M := by
  simp only [quad, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem quad_smul (r : ℂ) (p : Fin N → ℂ) (c b : Fin N) (M : Matrix (Fin N) (Fin N) ℝ) :
    quad (r • p) c b M = r * quad p c b M := by
  simp only [quad, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- Columns of an orthogonal matrix are orthonormal, in complex form. -/
theorem sum_col_mul (k : unitaryCompact ℝ N) (c b : Fin N) :
    (∑ l, ((((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) l c : ℝ) : ℂ) *
      ((((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ) l b : ℝ) : ℂ)) =
      if c = b then 1 else 0 := by
  have h4 := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => A c b) (transpose_mul_self_of_mem k)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h4
  rw [← Complex.ofReal_inj] at h4
  push_cast at h4
  rw [h4]
  split_ifs <;> simp

/-! ## The reachable quadratic functions -/

/-- The `p ∈ ℂ^N` for which there are `G_c ∈ A` with `G_c(κ) = ∑_l p_l κ_{lc} κ_{lb}` on
`O(N)`. -/
def reach (A : Submodule ℂ (Langlands.GeneralLinear N ℝ → ℂ)) (b : Fin N) :
    Submodule ℂ (Fin N → ℂ) where
  carrier := {p | ∃ G : Fin N → Langlands.GeneralLinear N ℝ → ℂ, ∀ c, G c ∈ A ∧
    ∀ κ : unitaryCompact ℝ N, G c (κ : Langlands.GeneralLinear N ℝ) =
      quad p c b ((κ : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ)}
  zero_mem' := ⟨fun _ => 0, fun c => ⟨A.zero_mem, fun κ => by rw [quad_zero]; rfl⟩⟩
  add_mem' := by
    intro p q hp hq
    obtain ⟨G, hG⟩ := hp
    obtain ⟨G', hG'⟩ := hq
    exact ⟨fun c => G c + G' c, fun c => ⟨A.add_mem (hG c).1 (hG' c).1, fun κ => by
      show G c κ + G' c κ = _
      rw [quad_add, (hG c).2 κ, (hG' c).2 κ]⟩⟩
  smul_mem' := by
    intro r p hp
    obtain ⟨G, hG⟩ := hp
    exact ⟨fun c => r • G c, fun c => ⟨A.smul_mem r (hG c).1, fun κ => by
      show r * G c κ = _
      rw [quad_smul, (hG c).2 κ]⟩⟩

/-- The diagonal `s_l = e_l + (N - 1)/2` of the operator `S`. -/
def sVec (N : ℕ) (e : ℕ → ℂ) (l : Fin N) : ℂ :=
  (e l + ((N : ℂ) - 1) / 2 - ((l : ℕ) : ℂ)) + ((l : ℕ) : ℂ)

/-- The reachable vectors are stable under `S`. -/
theorem sOp_mem_reach (hχ : IsSignedPower χ e) {A : Submodule ℂ (Langlands.GeneralLinear N ℝ → ℂ)}
    (hA : A ≤ kFiniteFunctions (principalSeries ℝ N χ) (unitaryCompact ℝ N))
    (hAD : ∀ (X : Matrix (Fin N) (Fin N) ℝ), ∀ w ∈ A, rightDerivative (matrixModel ℝ N) X w ∈ A)
    (b : Fin N) {p : Fin N → ℂ} (hp : p ∈ reach A b) : sOp (sVec N e) p ∈ reach A b := by
  obtain ⟨G, hG⟩ := hp
  refine ⟨fun a => ∑ c, rightDerivative (matrixModel ℝ N) (Matrix.single a c (1 : ℝ)) (G c),
    fun a => ⟨A.sum_mem fun c _ => hAD _ _ (hG c).1, fun κ => ?_⟩⟩
  have hs := sum_rightDerivative_single
    (α := fun i : Fin N => e i + ((N : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))
    (fun c => (hA (hG c).1).1.1) (fun c => isExpEquivariant_of_mem hχ (hA (hG c).1).1) p b
    (fun c => (hG c).2) a κ
  beta_reduce
  rw [Finset.sum_apply, hs]
  rfl

/-- The spherical vector is `1` on `O(N)`. -/
theorem spherical_of_mem (κ : unitaryCompact ℝ N) :
    signVector N e (fun _ => 0) (fun _ => 0) (κ : Langlands.GeneralLinear N ℝ) = 1 := by
  rw [signVector_of_mem _ _ κ.2, signMonomial]
  simp

/-- The all-ones vector is reachable from the spherical vector. -/
theorem one_mem_reach {A : Submodule ℂ (Langlands.GeneralLinear N ℝ → ℂ)}
    (hT : signVector N e (fun _ => 0) (fun _ => 0) ∈ A) (b : Fin N) :
    (fun _ => (1 : ℂ)) ∈ reach A b := by
  refine ⟨fun c => if c = b then signVector N e (fun _ => 0) (fun _ => 0) else 0,
    fun c => ⟨?_, fun κ => ?_⟩⟩
  · beta_reduce
    split_ifs
    · exact hT
    · exact A.zero_mem
  · simp only [quad, one_mul]
    rw [sum_col_mul]
    split_ifs
    · exact spherical_of_mem κ
    · rfl

/-! ## The regularized vector -/

/-- **The regularized vector lies in the Lie span.** Let `A` be a subspace of the `O(m+1)`-finite
functions of the principal series of `χ` (signed powers with exponents `e`, trivial signs), stable
under right derivatives and containing the spherical vector. If `e_m - e_j - 1 ≠ 0` for `j < m`,
then `A` contains the function with restriction `κ ↦ κ_{mm}²` to `O(m+1)`. -/
theorem regularized_mem {m : ℕ} (hχ : IsSignedPower χ e) (hp : ∀ l, χ l (-1) = 1)
    {A : Submodule ℂ (Langlands.GeneralLinear (m + 1) ℝ → ℂ)}
    (hA : A ≤ kFiniteFunctions (principalSeries ℝ (m + 1) χ) (unitaryCompact ℝ (m + 1)))
    (hAD : ∀ (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ), ∀ w ∈ A,
      rightDerivative (matrixModel ℝ (m + 1)) X w ∈ A)
    (he : ∀ j : ℕ, j < m → e m - e j - 1 ≠ 0)
    (hT : signVector (m + 1) e (fun _ => 0) (fun _ => 0) ∈ A) :
    signVector (m + 1) e (fun _ => 0) (bump (fun _ => 0) m 1) ∈ A := by
  have hs : ∀ j : Fin (m + 1), j ≠ Fin.last m →
      sVec (m + 1) e (Fin.last m) - sVec (m + 1) e j - 1 ≠ 0 := by
    intro j hj
    have hjm : (j : ℕ) < m := lt_of_le_of_ne (Nat.lt_succ_iff.mp j.isLt)
      (fun h => hj (Fin.ext (by rw [h, Fin.val_last])))
    have h1 := he j hjm
    have h2 : sVec (m + 1) e (Fin.last m) - sVec (m + 1) e j - 1 = e m - e j - 1 := by
      simp only [sVec, Fin.val_last]
      ring
    rw [h2]
    exact h1
  have hmem := single_last_mem m (sVec (m + 1) e) hs (reach A (Fin.last m))
    (fun p hp => sOp_mem_reach hχ hA hAD _ hp) 1 (by rw [Polynomial.eval_one]; exact one_ne_zero)
    (by rw [map_one, Module.End.one_apply]; exact one_mem_reach hT _)
  obtain ⟨G, hG⟩ := hmem
  have hp' : ∀ l, χ l (-1) = (-1) ^ (fun _ => 0 : ℕ → ℕ) l := fun l => by rw [hp l, pow_zero]
  have hH := signVector_mem (n := m + 1) (fun _ => 0) (bump (fun _ => 0) m 1) hχ hp'
  have heq : G (Fin.last m) = signVector (m + 1) e (fun _ => 0) (bump (fun _ => 0) m 1) := by
    refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries (hA (hG _).1).1 hH.1 fun k hk => ?_
    have h1 := (hG (Fin.last m)).2 ⟨k, hk⟩
    change G (Fin.last m) k = _ at h1
    rw [h1, signVector_of_mem _ _ hk, signMonomial, quad, Fin.prod_univ_castSucc]
    have hcs : ∀ l : Fin m, bump (fun _ => 0) m 1 ((Fin.castSucc l : Fin (m + 1)) : ℕ) = 0 :=
      fun l => by simp [bump, (Fin.isLt l).ne]
    have hlast : bump (fun _ => 0) m 1 ((Fin.last m : Fin (m + 1)) : ℕ) = 1 := by
      simp [bump]
    simp only [hcs, hlast, mul_zero, add_zero, zero_add, pow_zero, Finset.prod_const_one,
      one_mul, Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    simp
    ring
  rw [← heq]
  exact (hG _).1

end RealSphericalReach

end Langlands.Archimedean
