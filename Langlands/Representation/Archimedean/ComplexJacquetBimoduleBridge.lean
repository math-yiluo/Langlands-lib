import Langlands.Representation.Archimedean.ComplexJacquetBimodule
import Langlands.Representation.Archimedean.ComplexJacquetOneSided
import Langlands.Representation.Archimedean.ComplexJacquetTorus
import Mathlib.LinearAlgebra.Eigenspace.Pi

/-!
# From Harish-Chandra bimodules to one-sided nonvanishing of the Jacquet module

`complexJacquetOneSided_of_bimodule` derives `ComplexJacquetOneSidedStatement` from
`ComplexJacquetBimoduleStatement`. An irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module `(ρ, π)`
carries the two commuting actions `ℓ(Y) = π̃(Y, 0)` and `r(Y) = π̃(0, Y)` of `𝔤𝔩_n(ℂ)`, where
`π̃ = ComplexGenericLarge.prodAction π` is `π` transported to `𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)`. The
subspace `E` is the `U(n)`-span of a nonzero vector. See the paired Markdown.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace ComplexJacquetBimoduleBridge

open ComplexGenericLarge ComplexJacquetFinite InfinitesimalCharacter

/-! ## The two factors -/

section Factors

variable {n : ℕ}

/-- The inclusion `Y ↦ Pi.single i Y` of the factor `i` of `𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)`. -/
def factorHom (i : Fin 2) :
    Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ (Fin 2 → Matrix (Fin n) (Fin n) ℂ) :=
  { LinearMap.single ℂ (fun _ : Fin 2 => Matrix (Fin n) (Fin n) ℂ) i with
    map_lie' := by
      intro X Y
      change (Pi.single i ⁅X, Y⁆ : Fin 2 → Matrix (Fin n) (Fin n) ℂ) =
        ⁅(Pi.single i X : Fin 2 → Matrix (Fin n) (Fin n) ℂ), Pi.single i Y⁆
      rw [Ring.lie_def, Ring.lie_def, Pi.single_sub, Pi.single_mul, Pi.single_mul] }

theorem factorHom_apply (i : Fin 2) (Y : Matrix (Fin n) (Fin n) ℂ) :
    factorHom i Y = Pi.single i Y :=
  rfl

theorem single_zero_mul_single_one (X Y : Matrix (Fin n) (Fin n) ℂ) :
    (Pi.single 0 X : Fin 2 → Matrix (Fin n) (Fin n) ℂ) * Pi.single 1 Y = 0 := by
  funext t
  fin_cases t <;> simp

theorem single_one_mul_single_zero (X Y : Matrix (Fin n) (Fin n) ℂ) :
    (Pi.single 1 Y : Fin 2 → Matrix (Fin n) (Fin n) ℂ) * Pi.single 0 X = 0 := by
  funext t
  fin_cases t <;> simp

theorem eq_single_add_single (Y : Fin 2 → Matrix (Fin n) (Fin n) ℂ) :
    Y = Pi.single 0 (Y 0) + Pi.single 1 (Y 1) := by
  funext t
  fin_cases t <;> simp

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- The action `ℓ(Y) = π̃(Y, 0)` of the first factor. -/
def leftAct : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V :=
  (prodAction π).comp (factorHom 0)

/-- The action `r(Y) = π̃(0, Y)` of the second factor. -/
def rightAct : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V :=
  (prodAction π).comp (factorHom 1)

theorem leftAct_apply (Y : Matrix (Fin n) (Fin n) ℂ) :
    leftAct π Y = prodAction π (Pi.single 0 Y) :=
  rfl

theorem rightAct_apply (Y : Matrix (Fin n) (Fin n) ℂ) :
    rightAct π Y = prodAction π (Pi.single 1 Y) :=
  rfl

theorem leftAct_single (p q : Fin n) : leftAct π (Matrix.single p q 1) = ee π 0 p q :=
  rfl

theorem rightAct_single (p q : Fin n) : rightAct π (Matrix.single p q 1) = ee π 1 p q :=
  rfl

/-- The two factors commute. -/
theorem leftAct_mul_rightAct (X Y : Matrix (Fin n) (Fin n) ℂ) :
    leftAct π X * rightAct π Y = rightAct π Y * leftAct π X := by
  rw [← sub_eq_zero, leftAct_apply, rightAct_apply, prodAction_mul_sub,
    single_zero_mul_single_one, single_one_mul_single_zero, sub_zero, map_zero]

/-- `π(x) = ℓ(x₀) + r(x₁)` for `(x₀, x₁)` the image of `x` in `𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)`. -/
theorem pi_eq_left_add_right (x : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    π x = leftAct π (tensorEquiv x 0) + rightAct π (tensorEquiv x 1) := by
  rw [leftAct_apply, rightAct_apply, ← map_add, ← eq_single_add_single, prodAction_apply,
    AlgEquiv.symm_apply_apply]

/-- For a skew-Hermitian `Y`, `π(1 ⊗ Y) = ℓ(Y) - r(Yᵀ)`. -/
theorem pi_skew_eq {Y : Matrix (Fin n) (Fin n) ℂ} (hY : star Y = -Y) :
    π ((1 : ℂ) ⊗ₜ[ℝ] Y) = leftAct π Y - rightAct π Y.transpose := by
  have hconj : conjMat Y = -Y.transpose := by
    ext p q
    have h := congrFun (congrFun hY q) p
    rw [Matrix.star_apply, Matrix.neg_apply] at h
    rw [conjMat_apply, Matrix.neg_apply, Matrix.transpose_apply, ← h]
    rfl
  rw [← tensorEquiv_symm_pairHom, ← prodAction_apply, eq_single_add_single (pairHom Y),
    pairHom_zero, pairHom_one, hconj, map_add, leftAct_apply, rightAct_apply, Pi.single_neg,
    map_neg, sub_eq_add_neg]

/-- The `𝔨`-action `κ(Y) = ℓ(Y) - r(Yᵀ)` preserves every `U(n)`-stable subspace. -/
theorem kappa_mem {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
    (hgk : IsComplexGKModule n ρ π) (W : Submodule ℂ V) (hWK : ∀ k, ∀ w ∈ W, ρ k w ∈ W)
    (Y : Matrix (Fin n) (Fin n) ℂ) {w : V} (hw : w ∈ W) :
    leftAct π Y w - rightAct π Y.transpose w ∈ W := by
  set A : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (Y - star Y) with hA
  set B : Matrix (Fin n) (Fin n) ℂ := (-(Complex.I / 2)) • (Y + star Y) with hB
  have hA' : star A = -A := by
    rw [hA, star_smul, star_sub, star_star]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this]
    module
  have hB' : star B = -B := by
    rw [hB, star_smul, star_add, star_star]
    have : star (-(Complex.I / 2)) = Complex.I / 2 := by
      rw [star_neg, star_div₀, Complex.star_def, Complex.conj_I, map_ofNat, neg_div, neg_neg]
    rw [this]
    module
  have hYAB : Y = A + Complex.I • B := by
    rw [hA, hB, smul_smul]
    have : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [this]
    module
  have hk : ∀ Z : Matrix (Fin n) (Fin n) ℂ, star Z = -Z →
      leftAct π Z w - rightAct π Z.transpose w ∈ W := by
    intro Z hZ
    rw [← LinearMap.sub_apply, ← pi_skew_eq π hZ]
    exact skew_stable hgk W hWK Z hZ w hw
  have hsplit : leftAct π Y w - rightAct π Y.transpose w =
      (leftAct π A w - rightAct π A.transpose w) +
        Complex.I • (leftAct π B w - rightAct π B.transpose w) := by
    conv_lhs => rw [hYAB]
    simp only [Matrix.transpose_add, Matrix.transpose_smul, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, smul_sub]
    abel
  rw [hsplit]
  exact W.add_mem (hk A hA') (W.smul_mem _ (hk B hB'))

/-- `ρ(k) ℓ(Y) = ℓ(k Y k*) ρ(k)`. -/
theorem rho_leftAct {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
    (hgk : IsComplexGKModule n ρ π) (k : Matrix.unitaryGroup (Fin n) ℂ)
    (Y : Matrix (Fin n) (Fin n) ℂ) (v : V) :
    ρ k (leftAct π Y v) =
      leftAct π ((k : Matrix (Fin n) (Fin n) ℂ) * Y * (star k : Matrix (Fin n) (Fin n) ℂ))
        (ρ k v) := by
  have h := LinearMap.congr_fun (rho_mul_pi hgk.2.2.2 k (tensorEquiv.symm (Pi.single 0 Y))) v
  simp only [Module.End.mul_apply] at h
  rw [leftAct_apply, prodAction_apply, h, leftAct_apply, prodAction_apply]
  congr 2
  rw [← tensorEquiv_symm_pairHom, ← tensorEquiv_symm_pairHom, ← map_mul, ← map_mul]
  congr 1
  funext t
  fin_cases t
  · simp [pairHom_zero]
  · simp

end Factors

/-! ## The diagonal unitary circles -/

section Circle

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}

/-- `D_p = E^{(0)}_pp - E^{(1)}_pp`, i.e. `ℓ(E_pp) - r(E_pp)`. -/
abbrev diagDiff (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V) (p : Fin n) :
    Module.End ℂ V :=
  ee π 0 p p - ee π 1 p p

theorem star_single_I (p : Fin n) :
    star (Matrix.single p p Complex.I) = -Matrix.single p p Complex.I := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, Complex.star_def,
    Complex.conj_I, Matrix.single_neg]

/-- `π(1 ⊗ i E_pp) = i D_p`. -/
theorem pi_single_I (p : Fin n) (w : V) :
    π ((1 : ℂ) ⊗ₜ[ℝ] Matrix.single p p Complex.I) w = Complex.I • diagDiff π p w := by
  rw [pi_single_diag_eq]
  simp only [map_add, map_mul, MvPolynomial.algHom_C, diagAct_X, diagGen, LinearMap.add_apply,
    Module.End.mul_apply, Module.algebraMap_end_apply, Complex.conj_I, neg_smul, smul_sub,
    LinearMap.sub_apply]
  abel

/-- The circle `t ↦ exp(t i E_pp)` in `U(n)`. -/
abbrev circle (p : Fin n) (t : ℝ) : Matrix.unitaryGroup (Fin n) ℂ :=
  skewExp (t • Matrix.single p p Complex.I) (star_real_smul_of_skew (star_single_I p) t)

theorem smul_single_I_eq_diagI (p : Fin n) (t : ℝ) :
    t • Matrix.single p p Complex.I = diagI (Pi.single p t) := by
  ext i j
  simp only [diagI, Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply,
    Pi.single_apply]
  by_cases hij : i = j
  · subst hij
    split_ifs <;> simp_all [Complex.real_smul]
  · have hpij : ¬(p = i ∧ p = j) := fun h => hij (h.1.symm.trans h.2)
    simp [hij, hpij]

theorem circle_two_pi (p : Fin n) : circle p (2 * Real.pi) = 1 := by
  apply Subtype.ext
  rw [coe_skewExp, smul_single_I_eq_diagI, exp_diagI]
  show _ = (1 : Matrix (Fin n) (Fin n) ℂ)
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases hi : i = p
  · subst hi
    simp only [Pi.single_eq_same]
    push_cast
    exact Complex.exp_two_pi_mul_I
  · simp [hi]

theorem circle_zero (p : Fin n) : circle p 0 = 1 :=
  skewExp_zero_smul (star_single_I p)

/-- Along the circle, `t ↦ μ(ρ(exp(t i E_pp)) w)` has derivative `i μ(ρ(exp(s i E_pp)) D_p w)`
at `s`. -/
theorem hasDerivAt_circle (hgk : IsComplexGKModule n ρ π) (p : Fin n) (μ : V →ₗ[ℂ] ℂ) (w : V)
    (s : ℝ) :
    HasDerivAt (fun t => μ (ρ (circle p t) w))
      (Complex.I * μ (ρ (circle p s) (diagDiff π p w))) s := by
  have h := hasDerivAt_skewExp hgk (star_single_I p) μ w s
  rw [pi_single_I, map_smul, map_smul, smul_eq_mul] at h
  exact h

/-- On an eigenvector `D_p u = c u`, `μ(ρ(exp(t i E_pp)) u) = exp(i c t) μ(u)`. -/
theorem apply_circle_of_eigen (hgk : IsComplexGKModule n ρ π) (p : Fin n) (μ : V →ₗ[ℂ] ℂ)
    {u : V} {c : ℂ} (hu : diagDiff π p u = c • u) (t : ℝ) :
    μ (ρ (circle p t) u) = Complex.exp (Complex.I * c * t) * μ u := by
  have hd : ∀ s, HasDerivAt (fun t => μ (ρ (circle p t) u))
      (Complex.I * c * μ (ρ (circle p s) u)) s := by
    intro s
    have h := hasDerivAt_circle hgk p μ u s
    rw [hu, map_smul, map_smul, smul_eq_mul, ← mul_assoc] at h
    exact h
  have h := Langlands.Automorphic.OperatorRealization.eq_exp_mul_of_hasDerivAt hd t
  rw [h, circle_zero, map_one, Module.End.one_apply]

theorem exp_eq_one_of_eigen (hgk : IsComplexGKModule n ρ π) (p : Fin n) {u : V} {c : ℂ}
    (hu : diagDiff π p u = c • u) (hu0 : u ≠ 0) :
    Complex.exp (Complex.I * c * (2 * Real.pi : ℝ)) = 1 := by
  obtain ⟨μ, hμ⟩ : ∃ μ : Module.Dual ℂ V, μ u ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 ((Module.forall_dual_apply_eq_zero_iff ℂ u).1 h)
  have h := apply_circle_of_eigen hgk p μ hu (2 * Real.pi)
  rw [circle_two_pi, map_one, Module.End.one_apply] at h
  have h2 : Complex.exp (Complex.I * c * (2 * Real.pi : ℝ)) * μ u = 1 * μ u := by
    rw [one_mul]; exact h.symm
  exact mul_right_cancel₀ hμ h2

/-- **Integrality.** An eigenvalue of `D_p` is an integer. -/
theorem eigen_int (hgk : IsComplexGKModule n ρ π) (p : Fin n) {u : V} {c : ℂ}
    (hu : diagDiff π p u = c • u) (hu0 : u ≠ 0) : ∃ m : ℤ, c = m := by
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp (exp_eq_one_of_eigen hgk p hu hu0)
  refine ⟨m, ?_⟩
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply mul_left_cancel₀ hpi
  push_cast at hm
  linear_combination hm

/-- **No Jordan blocks.** If `D_p u = c u` and `D_p w = c w + u`, then `u = 0`. -/
theorem eq_zero_of_jordan (hgk : IsComplexGKModule n ρ π) (p : Fin n) {u w : V} {c : ℂ}
    (hu : diagDiff π p u = c • u) (hw : diagDiff π p w = c • w + u) : u = 0 := by
  by_contra hu0
  obtain ⟨μ, hμ⟩ : ∃ μ : Module.Dual ℂ V, μ u ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 ((Module.forall_dual_apply_eq_zero_iff ℂ u).1 h)
  set g : ℝ → ℂ := fun t => μ (ρ (circle p t) w) with hg
  have hgd : ∀ s, HasDerivAt g
      (Complex.I * c * g s + Complex.I * (Complex.exp (Complex.I * c * s) * μ u)) s := by
    intro s
    have h := hasDerivAt_circle hgk p μ w s
    rw [hw, map_add, map_add, map_smul, map_smul, smul_eq_mul,
      apply_circle_of_eigen hgk p μ hu s] at h
    convert h using 1
    ring
  set F : ℝ → ℂ := fun t => Complex.exp (-(Complex.I * c * t)) * g t - Complex.I * t * μ u
    with hF
  have hFd : ∀ s, HasDerivAt F 0 s := by
    intro s
    have h1 : HasDerivAt (fun t : ℝ => -(Complex.I * c * (t : ℂ))) (-(Complex.I * c * 1)) s :=
      ((hasDerivAt_id s).ofReal_comp.const_mul (Complex.I * c)).neg
    have h2 := h1.cexp.mul (hgd s)
    have h3 : HasDerivAt (fun t : ℝ => Complex.I * (t : ℂ) * μ u) (Complex.I * 1 * μ u) s :=
      ((hasDerivAt_id s).ofReal_comp.const_mul Complex.I).mul_const (μ u)
    have h4 := h2.sub h3
    convert h4 using 1
    rw [mul_add, ← mul_assoc (Complex.exp _) Complex.I, mul_comm (Complex.exp _) Complex.I,
      mul_assoc Complex.I (Complex.exp _), ← mul_assoc (Complex.exp _) (Complex.exp _),
      ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    ring
  have hc := is_const_of_deriv_eq_zero (fun s => (hFd s).differentiableAt)
    (fun s => (hFd s).deriv) (2 * Real.pi) 0
  have hg2 : g (2 * Real.pi) = g 0 := by
    simp only [hg, circle_two_pi, circle_zero]
  have he : Complex.exp (-(Complex.I * c * (2 * Real.pi : ℝ))) = 1 := by
    rw [Complex.exp_neg, exp_eq_one_of_eigen hgk p hu hu0, inv_one]
  simp only [hF, hg2, he, one_mul, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
    zero_mul, sub_zero] at hc
  have h5 : Complex.I * ((2 * Real.pi : ℝ) : ℂ) * μ u = 0 := by linear_combination -hc
  rcases mul_eq_zero.1 h5 with h6 | h6
  · rcases mul_eq_zero.1 h6 with h7 | h7
    · exact Complex.I_ne_zero h7
    · exact (mul_ne_zero two_ne_zero Real.pi_ne_zero) (Complex.ofReal_eq_zero.1 h7)
  · exact hμ h6

end Circle

/-! ## Joint eigenvectors on a `U(n)`-stable finite-dimensional subspace -/

section Joint

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}

theorem commute_diagDiff (p q : Fin n) : Commute (diagDiff π p) (diagDiff π q) :=
  ((commute_ee π 0 0 p q).sub_right (commute_ee π 0 1 p q)).sub_left
    ((commute_ee π 1 0 p q).sub_right (commute_ee π 1 1 p q))

/-- A finite-dimensional `U(n)`-stable subspace is spanned by joint eigenvectors of the `D_p`
with integer eigenvalues. -/
theorem le_span_joint (hgk : IsComplexGKModule n ρ π) (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] (hWK : ∀ k, ∀ w ∈ W, ρ k w ∈ W) :
    W ≤ Submodule.span ℂ {e | e ∈ W ∧ ∃ m : Fin n → ℤ, ∀ p : Fin n,
      diagDiff π p e = (m p : ℂ) • e} := by
  classical
  set S := Submodule.span ℂ {e | e ∈ W ∧ ∃ m : Fin n → ℤ, ∀ p : Fin n,
      diagDiff π p e = (m p : ℂ) • e} with hS
  have hmaps : ∀ p, ∀ w ∈ W, diagDiff π p w ∈ W := fun p w hw =>
    diag_sub_mem π hgk W hWK p hw
  let f : Fin n → Module.End ℂ W := fun p => (diagDiff π p).restrict (hmaps p)
  have hf : ∀ p (x : W), ((f p x : W) : V) = diagDiff π p x := fun p x => rfl
  have hcomm : Pairwise fun p q => Commute (f p) (f q) := by
    intro p q _
    rw [Commute, SemiconjBy]
    ext x
    simp only [Module.End.mul_apply, hf]
    exact LinearMap.congr_fun (commute_diagDiff (π := π) p q).eq x
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f hcomm fun p => Module.End.iSup_maxGenEigenspace_eq_top (f p)
  -- no Jordan blocks on `W`
  have hJ : ∀ p (c : ℂ) (y : W), (f p - c • 1) ((f p - c • 1) y) = 0 → (f p - c • 1) y = 0 := by
    intro p c y hy
    have hu_def : (((f p - c • 1) y : W) : V) = diagDiff π p y - c • (y : V) := rfl
    have hy' : diagDiff π p (((f p - c • 1) y : W) : V) -
        c • (((f p - c • 1) y : W) : V) = 0 :=
      congrArg (fun z : W => (z : V)) hy
    apply Subtype.ext
    rw [Submodule.coe_zero]
    refine eq_zero_of_jordan hgk p (c := c) (w := (y : V)) (sub_eq_zero.1 hy') ?_
    rw [hu_def]
    abel
  have hpow : ∀ p (c : ℂ) (k : ℕ) (x : W), ((f p - c • 1) ^ (k + 1)) x = 0 →
      (f p - c • 1) x = 0 := by
    intro p c k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      apply ih
      rw [pow_succ', Module.End.mul_apply]
      apply hJ
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply] at hx
      exact hx
  have hmem : ∀ χ : Fin n → ℂ, ∀ x ∈ ⨅ p, (f p).maxGenEigenspace (χ p), (x : V) ∈ S := by
    intro χ x hx
    rw [Module.End.mem_iInf_maxGenEigenspace_iff] at hx
    have heig : ∀ p, diagDiff π p x = χ p • (x : V) := by
      intro p
      obtain ⟨k, hk⟩ := hx p
      have h1 : (f p - χ p • 1) x = 0 := by
        rcases k with _ | k
        · simp only [pow_zero, Module.End.one_apply] at hk
          rw [hk, map_zero]
        · exact hpow p (χ p) k x hk
      have h2 := congrArg (fun y : W => (y : V)) h1
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        Submodule.coe_sub, Submodule.coe_smul, hf, Submodule.coe_zero] at h2
      exact sub_eq_zero.1 h2
    by_cases hx0 : (x : V) = 0
    · rw [hx0]; exact S.zero_mem
    · have hint : ∀ p, ∃ m : ℤ, χ p = m := fun p => eigen_int hgk p (heig p) hx0
      choose m hm using hint
      refine Submodule.subset_span ⟨x.2, m, fun p => ?_⟩
      rw [heig p, hm p]
  intro w hw
  have hw' : (⟨w, hw⟩ : W) ∈ ⨆ χ : Fin n → ℂ, ⨅ p, (f p).maxGenEigenspace (χ p) := by
    rw [htop]; exact Submodule.mem_top
  exact Submodule.iSup_induction _ (motive := fun x : W => (x : V) ∈ S) hw'
    (fun χ x hx => hmem χ x hx) S.zero_mem (fun x y hx hy => S.add_mem hx hy)

end Joint

/-! ## Generation and the infinitesimal character -/

section Generation

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}

/-- A nonzero `U(n)`-stable subspace generates an irreducible module under the first factor. -/
theorem left_generates (hgk : IsComplexGKModule n ρ π) (hirr : IsIrreducibleGKModule ρ π)
    (E : Submodule ℂ V) (hEK : ∀ k, ∀ e ∈ E, ρ k e ∈ E) (hE0 : E ≠ ⊥)
    (S : Submodule ℂ V) (hES : E ≤ S) (hS : ∀ X, ∀ s ∈ S, leftAct π X s ∈ S) : S = ⊤ := by
  set G : Submodule ℂ V := sInf {T | E ≤ T ∧ ∀ X, ∀ s ∈ T, leftAct π X s ∈ T} with hGdef
  have hGl : ∀ X, ∀ s ∈ G, leftAct π X s ∈ G := fun X s hs =>
    Submodule.mem_sInf.2 fun T hT => hT.2 X s (Submodule.mem_sInf.1 hs T hT)
  have hEG : E ≤ G := le_sInf fun _ hT => hT.1
  have hGS : G ≤ S := sInf_le ⟨hES, hS⟩
  have hGr : ∀ Z, ∀ s ∈ G, rightAct π Z s ∈ G := by
    let G' : Submodule ℂ V := G ⊓ ⨅ Z : Matrix (Fin n) (Fin n) ℂ, G.comap (rightAct π Z)
    have hmem : ∀ s, s ∈ G' ↔ s ∈ G ∧ ∀ Z, rightAct π Z s ∈ G := by
      intro s
      simp only [G', Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
    have hle : G ≤ G' := by
      refine sInf_le ⟨fun e he => (hmem e).2 ⟨hEG he, fun Z => ?_⟩, fun X s hs => ?_⟩
      · have hk := kappa_mem π hgk E hEK Z.transpose he
        rw [Matrix.transpose_transpose] at hk
        have h : rightAct π Z e = leftAct π Z.transpose e -
            (leftAct π Z.transpose e - rightAct π Z e) := by abel
        rw [h]
        exact G.sub_mem (hGl _ _ (hEG he)) (hEG hk)
      · rw [hmem] at hs ⊢
        refine ⟨hGl X s hs.1, fun Z => ?_⟩
        rw [← Module.End.mul_apply, ← leftAct_mul_rightAct, Module.End.mul_apply]
        exact hGl X _ (hs.2 Z)
    exact fun Z s hs => ((hmem s).1 (hle hs)).2 Z
  have hGρ : ∀ k, ∀ s ∈ G, ρ k s ∈ G := by
    intro k
    have hle : G ≤ G.comap (ρ k) := by
      refine sInf_le ⟨fun e he => hEG (hEK k e he), fun X s hs => ?_⟩
      rw [Submodule.mem_comap] at hs ⊢
      rw [rho_leftAct π hgk]
      exact hGl _ _ hs
    exact fun s hs => hle hs
  have hGπ : ∀ x, ∀ s ∈ G, π x s ∈ G := by
    intro x s hs
    rw [pi_eq_left_add_right, LinearMap.add_apply]
    exact G.add_mem (hGl _ s hs) (hGr _ s hs)
  have hG : G = ⊤ := (hirr.2 G hGρ hGπ).resolve_left fun h => hE0 (le_bot_iff.1 (h ▸ hEG))
  exact eq_top_iff.2 (hG ▸ hGS)

/-- The algebra map `U(𝔤𝔩_n(ℂ)) → U(𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ))` induced by the first factor. -/
def envFactor : UniversalEnvelopingAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) →ₐ[ℂ]
    UniversalEnvelopingAlgebra ℂ (Fin 2 → Matrix (Fin n) (Fin n) ℂ) :=
  UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp (factorHom 0))

theorem envFactor_ι (Y : Matrix (Fin n) (Fin n) ℂ) :
    envFactor (UniversalEnvelopingAlgebra.ι ℂ Y) =
      UniversalEnvelopingAlgebra.ι ℂ (Pi.single 0 Y : Fin 2 → Matrix (Fin n) (Fin n) ℂ) := by
  simp [envFactor, factorHom_apply]

theorem envelopingAction_leftAct (u : UniversalEnvelopingAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) :
    envelopingAction (leftAct π) u = envelopingAction (prodAction π) (envFactor u) := by
  have h : envelopingAction (leftAct π) =
      (envelopingAction (prodAction π)).comp (envFactor (n := n)) := by
    apply UniversalEnvelopingAlgebra.hom_ext
    refine LieHom.ext fun Y => ?_
    simp [envFactor, leftAct, factorHom_apply]
  exact AlgHom.congr_fun h u

theorem ι_commute_ι (x y : Fin 2 → Matrix (Fin n) (Fin n) ℂ) (h : x * y = y * x) :
    Commute (UniversalEnvelopingAlgebra.ι ℂ x) (UniversalEnvelopingAlgebra.ι ℂ y) := by
  rw [Commute, SemiconjBy, ← sub_eq_zero, ← Ring.lie_def, ← LieHom.map_lie, Ring.lie_def, h,
    sub_self, map_zero]

/-- The second factor commutes with the image of `envFactor`. -/
theorem commute_envFactor (Y : Matrix (Fin n) (Fin n) ℂ)
    (a : UniversalEnvelopingAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) :
    Commute (UniversalEnvelopingAlgebra.ι ℂ (Pi.single 1 Y : Fin 2 → Matrix (Fin n) (Fin n) ℂ))
      (envFactor a) := by
  induction a using envInduction with
  | algebraMap r =>
    rw [AlgHom.commutes]
    exact Algebra.commute_algebraMap_right _ _
  | ι X =>
    rw [envFactor_ι]
    apply ι_commute_ι
    rw [single_one_mul_single_zero, single_zero_mul_single_one]
  | mul a b ha hb =>
    rw [map_mul]
    exact ha.mul_right hb
  | add a b ha hb =>
    rw [map_add]
    exact ha.add_right hb

/-- `envFactor` maps the center into the center. -/
theorem envFactor_mem_center {z : UniversalEnvelopingAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ)}
    (hz : z ∈ Subalgebra.center ℂ _) : envFactor z ∈ Subalgebra.center ℂ _ := by
  rw [Subalgebra.mem_center_iff]
  intro b
  have hc : Commute b (envFactor z) := by
    induction b using envInduction with
    | algebraMap r => exact Algebra.commute_algebraMap_left _ _
    | ι Y =>
      rw [eq_single_add_single Y, map_add]
      refine Commute.add_left ?_ (commute_envFactor _ z)
      rw [← envFactor_ι]
      have h := (Subalgebra.mem_center_iff.1 hz) (UniversalEnvelopingAlgebra.ι ℂ (Y 0))
      rw [Commute, SemiconjBy, ← map_mul, ← map_mul, h]
    | mul a b ha hb => exact ha.mul_left hb
    | add a b ha hb => exact ha.add_left hb
  exact hc.eq

/-- The first factor has an infinitesimal character. -/
theorem leftAct_hasInfinitesimalCharacter (hgk : IsComplexGKModule n ρ π)
    (hirr : IsIrreducibleGKModule ρ π) (hadm : IsAdmissibleGKModule ρ) :
    HasInfinitesimalCharacter (leftAct π) := by
  intro z hz
  obtain ⟨c, hc⟩ := prodAction_hasInfinitesimalCharacter hgk hirr hadm _ (envFactor_mem_center hz)
  exact ⟨c, by rw [envelopingAction_leftAct, hc]⟩

end Generation

end ComplexJacquetBimoduleBridge

universe uV

open ComplexJacquetBimoduleBridge in
/-- **One-sided nonvanishing from the bimodule statement.** `ComplexJacquetBimoduleStatement`,
applied to the two factors `ℓ`, `r` of an irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module and the
`U(n)`-span `E` of a nonzero vector, gives `ComplexJacquetOneSidedStatement`. -/
theorem complexJacquetOneSided_of_bimodule :
    ComplexJacquetBimoduleStatement.{uV} → ComplexJacquetOneSidedStatement.{uV} := by
  intro hB n V _ _ ρ π hgk hirr hadm
  have := hirr.1
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  set E := FiniteVectors.orbitSpan ρ v with hEdef
  have hEfin : FiniteDimensional ℂ E := hgk.1 v
  have hEK : ∀ k, ∀ e ∈ E, ρ k e ∈ E := fun k e he =>
    (FiniteVectors.orbitSubrepresentation ρ v).apply_mem_toSubmodule k he
  have hE0 : E ≠ ⊥ := fun h => hv ((Submodule.mem_bot ℂ).1
    (h ▸ FiniteVectors.self_mem_orbitSpan ρ v))
  have hspan := le_span_joint (π := π) hgk E hEK
  exact hB n V (leftAct π) (rightAct π) (leftAct_mul_rightAct π) E hEfin hE0
    (fun Y e he => kappa_mem π hgk E hEK Y he) hspan
    (left_generates hgk hirr E hEK hE0) (leftAct_hasInfinitesimalCharacter hgk hirr hadm)

end Langlands.Archimedean
