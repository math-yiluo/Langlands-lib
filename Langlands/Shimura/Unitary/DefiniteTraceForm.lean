import Langlands.Shimura.Unitary.Positivity
import Langlands.Shimura.Unitary.Adelic
import Langlands.Shimura.Unitary.RationalTrace
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix

/-!
# The trace form of an involution and its Gram matrices

For an involution `τ` of an `R`-algebra `B`, the symmetrized trace form
`T(y, z) = tr(L_{τ(y) z}) + tr(L_{τ(z) y})` is a symmetric bilinear form, and every `x` with
`τ(x) x = c` central satisfies `T(x y, x z) = c T(y, z)`. In a basis this says that the matrix
`X` of left multiplication by `x` satisfies `Xᵀ G X = c G` for the Gram matrix `G` of `T`. The
matrices of left and right multiplications commute, and a matrix commuting with all right
multiplications is a left multiplication.

For an involution `σ` of a finite-dimensional `ℚ`-algebra `A` whose real scalar extension is
positive, the trace form is positive definite, every quadratic form is bounded by a multiple of
it, and `Γᵀ G Γ = t G` for the matrix `Γ` of left multiplication by `γ` forces `σ(γ) γ = t`.
-/

noncomputable section

open scoped TensorProduct Matrix

namespace Langlands.Shimura.AlgebraInvolution

open Module Matrix

section General

variable {R : Type*} {B : Type*} [CommRing R] [Ring B] [Algebra R B]

/-- The symmetrized trace form `T(y, z) = tr(L_{τ(y) z}) + tr(L_{τ(z) y})` of an involution. -/
def traceForm (τ : AlgebraInvolution R B) : LinearMap.BilinForm R B :=
  (Langlands.Algebra.regularTraceForm R B).comp τ.linear LinearMap.id +
    ((Langlands.Algebra.regularTraceForm R B).comp τ.linear LinearMap.id).flip

theorem traceForm_apply (τ : AlgebraInvolution R B) (y z : B) :
    τ.traceForm y z = Langlands.Algebra.regularTrace R B (τ y * z) +
      Langlands.Algebra.regularTrace R B (τ z * y) :=
  rfl

theorem traceForm_comm (τ : AlgebraInvolution R B) (y z : B) :
    τ.traceForm y z = τ.traceForm z y := by
  rw [traceForm_apply, traceForm_apply, add_comm]

theorem traceForm_isSymm (τ : AlgebraInvolution R B) : τ.traceForm.IsSymm :=
  ⟨fun y z => traceForm_comm τ y z⟩

/-- Elements with `τ(x) x = c` are similitudes of the trace form: `T(x y, x z) = c T(y, z)`. -/
theorem traceForm_mul_mul (τ : AlgebraInvolution R B) {x : B} {c : R}
    (hx : τ x * x = algebraMap R B c) (y z : B) :
    τ.traceForm (x * y) (x * z) = c * τ.traceForm y z := by
  have h : ∀ y z : B, τ (x * y) * (x * z) = c • (τ y * z) := fun y z => by
    rw [τ.apply_mul, mul_assoc, ← mul_assoc (τ x) x z, hx, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, mul_smul_comm]
  rw [traceForm_apply, traceForm_apply, h, h, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    mul_add]

/-- If `x τ(x) = c` for a unit `x`, then also `τ(x) x = c`. -/
theorem apply_mul_self_of_mul_apply (τ : AlgebraInvolution R B) {x : Bˣ} {c : R}
    (hx : (x : B) * τ x = algebraMap R B c) : τ x * x = algebraMap R B c := by
  have h : τ x = ((x⁻¹ : Bˣ) : B) * algebraMap R B c := by
    rw [← hx, ← mul_assoc, Units.inv_mul, one_mul]
  rw [h, mul_assoc, Algebra.commutes c (x : B), ← mul_assoc, Units.inv_mul, one_mul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Gram matrices of similitudes.** If `τ(x) x = c`, the matrix `X` of left multiplication by
`x` satisfies `Xᵀ G X = c G` for the Gram matrix `G` of the trace form. -/
theorem leftMulMatrix_transpose_mul_toMatrix_traceForm (τ : AlgebraInvolution R B)
    (b : Basis ι R B) {x : B} {c : R} (hx : τ x * x = algebraMap R B c) :
    (Algebra.leftMulMatrix b x)ᵀ * LinearMap.BilinForm.toMatrix b τ.traceForm *
        Algebra.leftMulMatrix b x =
      c • LinearMap.BilinForm.toMatrix b τ.traceForm := by
  rw [Algebra.leftMulMatrix_apply, ← LinearMap.BilinForm.toMatrix_comp, ← map_smul]
  congr 1
  ext y z
  exact traceForm_mul_mul τ hx y z

/-- The matrix of right multiplication by `y` in the basis `b`. -/
def rightMulMatrix (b : Basis ι R B) (y : B) : Matrix ι ι R :=
  LinearMap.toMatrix b b (LinearMap.mulRight R y)

theorem rightMulMatrix_apply (b : Basis ι R B) (y : B) (i j : ι) :
    rightMulMatrix b y i j = b.repr (b j * y) i :=
  LinearMap.toMatrix_apply _ _ _ _ _

/-- Left and right multiplications commute. -/
theorem leftMulMatrix_mul_rightMulMatrix (b : Basis ι R B) (x y : B) :
    Algebra.leftMulMatrix b x * rightMulMatrix b y =
      rightMulMatrix b y * Algebra.leftMulMatrix b x := by
  rw [Algebra.leftMulMatrix_apply, rightMulMatrix, ← LinearMap.toMatrix_mul,
    ← LinearMap.toMatrix_mul]
  congr 1
  ext z
  simp [mul_assoc]

/-- A matrix commuting with the right multiplications by the basis vectors is the matrix of a
left multiplication. -/
theorem exists_leftMulMatrix_eq (b : Basis ι R B) (M : Matrix ι ι R)
    (hM : ∀ k, M * rightMulMatrix b (b k) = rightMulMatrix b (b k) * M) :
    ∃ γ : B, Algebra.leftMulMatrix b γ = M := by
  set Γ := Matrix.toLin b b M
  have hk : ∀ k z, Γ (z * b k) = Γ z * b k := by
    intro k z
    have h := congrArg (Matrix.toLin b b) (hM k)
    rw [Matrix.toLin_mul b b b, Matrix.toLin_mul b b b, rightMulMatrix,
      Matrix.toLin_toMatrix] at h
    exact LinearMap.congr_fun h z
  have hall : ∀ z a, Γ (z * a) = Γ z * a := by
    intro z a
    conv_lhs => rw [← b.sum_repr a]
    conv_rhs => rw [← b.sum_repr a]
    simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, hk]
  refine ⟨Γ 1, ?_⟩
  have h1 : Algebra.lmul R B (Γ 1) = Γ := by
    ext a
    change Γ 1 * a = Γ a
    rw [← hall, one_mul]
  rw [Algebra.leftMulMatrix_apply, h1, LinearMap.toMatrix_toLin]

end General

section BaseChange

variable {R : Type*} {B : Type*} [CommRing R] [Ring B] [Algebra R B]
variable (S : Type*) [CommRing S] [Algebra R S]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem traceForm_baseChange_tmul [Module.Free R B] [Module.Finite R B]
    (σ : AlgebraInvolution R B) (y z : B) :
    (σ.baseChange S).traceForm ((1 : S) ⊗ₜ[R] y) ((1 : S) ⊗ₜ[R] z) =
      algebraMap R S (σ.traceForm y z) := by
  rw [traceForm_apply, traceForm_apply, baseChange_tmul, baseChange_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Langlands.Algebra.regularTrace_one_tmul, Langlands.Algebra.regularTrace_one_tmul, ← map_add]

/-- The Gram matrix of the scalar-extended trace form in the scalar-extended basis. -/
theorem toMatrix_traceForm_baseChange [Module.Free R B] [Module.Finite R B]
    (σ : AlgebraInvolution R B) (b : Basis ι R B) :
    LinearMap.BilinForm.toMatrix (Algebra.TensorProduct.basis S b) (σ.baseChange S).traceForm =
      (LinearMap.BilinForm.toMatrix b σ.traceForm).map (algebraMap R S) := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, Matrix.map_apply, LinearMap.BilinForm.toMatrix_apply,
    Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
    traceForm_baseChange_tmul]

theorem leftMulMatrix_one_tmul (b : Basis ι R B) (y : B) :
    Algebra.leftMulMatrix (Algebra.TensorProduct.basis S b) ((1 : S) ⊗ₜ[R] y) =
      (Algebra.leftMulMatrix b y).map (algebraMap R S) := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem rightMulMatrix_one_tmul (b : Basis ι R B) (y : B) :
    rightMulMatrix (Algebra.TensorProduct.basis S b) ((1 : S) ⊗ₜ[R] y) =
      (rightMulMatrix b y).map (algebraMap R S) := by
  ext i j
  rw [rightMulMatrix_apply, Matrix.map_apply, rightMulMatrix_apply,
    Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Algebra.TensorProduct.basis_repr_tmul]
  simp

/-- **Gram matrices of scalar-extended similitudes.** For a point `(x, c)` of the similitude
group over `S`, the matrix `X` of left multiplication by `x` in the scalar-extended basis
satisfies `Xᵀ G X = c G`, where `G` is the rational Gram matrix of the trace form. -/
theorem points_leftMulMatrix_transpose_mul_gram [Module.Free R B] [Module.Finite R B]
    (σ : AlgebraInvolution R B) (b : Basis ι R B) (g : σ.Points S) :
    (Algebra.leftMulMatrix (Algebra.TensorProduct.basis S b) (g.1.1 : S ⊗[R] B))ᵀ *
        (LinearMap.BilinForm.toMatrix b σ.traceForm).map (algebraMap R S) *
        Algebra.leftMulMatrix (Algebra.TensorProduct.basis S b) (g.1.1 : S ⊗[R] B) =
      (g.1.2 : S) • (LinearMap.BilinForm.toMatrix b σ.traceForm).map (algebraMap R S) := by
  rw [← toMatrix_traceForm_baseChange]
  exact leftMulMatrix_transpose_mul_toMatrix_traceForm _ _
    (apply_mul_self_of_mul_apply _ (((σ.baseChange S).mem_similitudes_iff g.1).1 g.2))

end BaseChange

section Real

variable {ι : Type*} [Fintype ι]

/-- A real quadratic form which is positive on nonzero vectors bounds every quadratic form up to
a constant. -/
theorem exists_dotProduct_mulVec_le (G H : Matrix ι ι ℝ)
    (hG : ∀ v : ι → ℝ, v ≠ 0 → 0 < v ⬝ᵥ G *ᵥ v) :
    ∃ C : ℝ, ∀ v : ι → ℝ, v ⬝ᵥ H *ᵥ v ≤ C * (v ⬝ᵥ G *ᵥ v) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, fun v => by simp [dotProduct]⟩
  let Q : (ι → ℝ) → ℝ := fun v => v ⬝ᵥ G *ᵥ v
  have hQcont : Continuous Q := by
    change Continuous fun v : ι → ℝ => v ⬝ᵥ G *ᵥ v
    fun_prop
  have hQsmul : ∀ (t : ℝ) v, Q (t • v) = t ^ 2 * Q v := by
    intro t v
    simp only [Q, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_sphere (0 : ι → ℝ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 zero_le_one) hQcont.continuousOn
  have hv₀0 : v₀ ≠ 0 := by
    rintro rfl
    simp at hv₀
  set m := Q v₀
  have hm : 0 < m := hG v₀ hv₀0
  have hlow : ∀ v, m * ‖v‖ ^ 2 ≤ Q v := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simpa using (hQsmul 0 0).ge
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
    have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : ι → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have h1 := hmin hu
    have h2 : Q v = ‖v‖ ^ 2 * Q (‖v‖⁻¹ • v) := by
      rw [← hQsmul, smul_smul, mul_inv_cancel₀ hn, one_smul]
    rw [h2, mul_comm m]
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  set M : ℝ := ∑ i, ∑ j, |H i j|
  have hup : ∀ v : ι → ℝ, v ⬝ᵥ H *ᵥ v ≤ M * ‖v‖ ^ 2 := by
    intro v
    have hv : ∀ i, |v i| ≤ ‖v‖ := fun i => by
      rw [← Real.norm_eq_abs]
      exact norm_le_pi_norm v i
    have e : v ⬝ᵥ H *ᵥ v = ∑ i, ∑ j, v i * H i j * v j := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    calc v i * H i j * v j ≤ |v i * H i j * v j| := le_abs_self _
      _ = |H i j| * (|v i| * |v j|) := by rw [abs_mul, abs_mul]; ring
      _ ≤ |H i j| * (‖v‖ * ‖v‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (hv i) (hv j) (abs_nonneg _) (norm_nonneg _)) (abs_nonneg _)
      _ = |H i j| * ‖v‖ ^ 2 := by ring
  refine ⟨M / m, fun v => ?_⟩
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  calc v ⬝ᵥ H *ᵥ v ≤ M * ‖v‖ ^ 2 := hup v
    _ = M / m * (m * ‖v‖ ^ 2) := by field_simp
    _ ≤ M / m * Q v := mul_le_mul_of_nonneg_left (hlow v) (div_nonneg hM hm.le)

end Real

section Positive

variable {B : Type*} [Ring B] [Algebra ℝ B]

/-- For a positive involution of a real algebra the trace form is positive definite. -/
theorem traceForm_self_pos_of_isPositive {τ : AlgebraInvolution ℝ B} (hpos : τ.IsPositive)
    {y : B} (hy : y ≠ 0) : 0 < τ.traceForm y y := by
  rw [traceForm_apply, Langlands.Algebra.regularTrace_apply]
  have := hpos y hy
  linarith

variable {A : Type*} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For an involution whose real scalar extension is positive, the trace form is positive
definite. -/
theorem traceForm_self_pos (σ : AlgebraInvolution ℚ A) (hpos : (σ.baseChange ℝ).IsPositive)
    {a : A} (ha : a ≠ 0) : 0 < σ.traceForm a a := by
  have h1 : (1 : ℝ) ⊗ₜ[ℚ] a ≠ 0 := by
    intro h
    apply ha
    apply Algebra.TensorProduct.includeRight_injective (A := ℝ) (algebraMap ℚ ℝ).injective
    rw [map_zero]
    exact h
  have h := traceForm_self_pos_of_isPositive hpos h1
  rw [traceForm_baseChange_tmul, eq_ratCast (algebraMap ℚ ℝ)] at h
  exact_mod_cast h

/-- The Gram matrix of the trace form of a positive involution is positive definite. -/
theorem dotProduct_toMatrix_traceForm_mulVec_pos (σ : AlgebraInvolution ℚ A)
    (hpos : (σ.baseChange ℝ).IsPositive) (b : Basis ι ℚ A) {v : ι → ℚ} (hv : v ≠ 0) :
    0 < v ⬝ᵥ LinearMap.BilinForm.toMatrix b σ.traceForm *ᵥ v := by
  have h := traceForm_self_pos σ hpos (a := b.equivFun.symm v)
    ((LinearEquiv.map_ne_zero_iff _).2 hv)
  rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b] at h
  have hv' : (b.repr (b.equivFun.symm v) : ι → ℚ) = v := b.equivFun.apply_symm_apply v
  rwa [hv'] at h

/-- For an involution whose real scalar extension is positive, every rational quadratic form is
bounded by a multiple of the trace form. -/
theorem exists_dotProduct_mulVec_le_traceForm (σ : AlgebraInvolution ℚ A)
    (hpos : (σ.baseChange ℝ).IsPositive) (b : Basis ι ℚ A) (H : Matrix ι ι ℚ) :
    ∃ C : ℕ, ∀ v : ι → ℚ,
      v ⬝ᵥ H *ᵥ v ≤ C * (v ⬝ᵥ LinearMap.BilinForm.toMatrix b σ.traceForm *ᵥ v) := by
  set G := LinearMap.BilinForm.toMatrix b σ.traceForm
  let bR := Algebra.TensorProduct.basis ℝ b
  have hG : ∀ v : ι → ℝ, v ≠ 0 → 0 < v ⬝ᵥ G.map (algebraMap ℚ ℝ) *ᵥ v := by
    intro v hv
    have h := traceForm_self_pos_of_isPositive hpos (y := bR.equivFun.symm v)
      ((LinearEquiv.map_ne_zero_iff _).2 hv)
    rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec bR,
      toMatrix_traceForm_baseChange] at h
    have hv' : (bR.repr (bR.equivFun.symm v) : ι → ℝ) = v := bR.equivFun.apply_symm_apply v
    rwa [hv'] at h
  obtain ⟨C, hC⟩ := exists_dotProduct_mulVec_le _ (H.map (algebraMap ℚ ℝ)) hG
  refine ⟨⌈C⌉₊, fun v => ?_⟩
  have hcast : ∀ M : Matrix ι ι ℚ, ((v ⬝ᵥ M *ᵥ v : ℚ) : ℝ) =
      (algebraMap ℚ ℝ ∘ v) ⬝ᵥ M.map (algebraMap ℚ ℝ) *ᵥ (algebraMap ℚ ℝ ∘ v) := by
    intro M
    rw [← eq_ratCast (algebraMap ℚ ℝ), RingHom.map_dotProduct]
    congr 1
    ext i
    exact RingHom.map_mulVec _ _ _ i
  have hQ : 0 ≤ (algebraMap ℚ ℝ ∘ v) ⬝ᵥ G.map (algebraMap ℚ ℝ) *ᵥ (algebraMap ℚ ℝ ∘ v) := by
    by_cases h0 : algebraMap ℚ ℝ ∘ v = 0
    · rw [h0]
      simp
    · exact (hG _ h0).le
  have : ((v ⬝ᵥ H *ᵥ v : ℚ) : ℝ) ≤ ((⌈C⌉₊ * (v ⬝ᵥ G *ᵥ v) : ℚ) : ℝ) := by
    rw [Rat.cast_mul, hcast, hcast, Rat.cast_natCast]
    exact (hC _).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil C) hQ)
  exact_mod_cast this

/-- **Recognizing similitudes.** For an involution whose real scalar extension is positive, if
left multiplication by `γ` multiplies the trace form by `t`, then `σ(γ) γ = t`. -/
theorem apply_mul_self_eq_of_traceForm (σ : AlgebraInvolution ℚ A)
    (hpos : (σ.baseChange ℝ).IsPositive) {γ : A} {t : ℚ}
    (h : ∀ y z, σ.traceForm (γ * y) (γ * z) = t * σ.traceForm y z) :
    σ γ * γ = algebraMap ℚ A t := by
  obtain ⟨w, hwdef⟩ : ∃ w : A, w = σ γ * γ - algebraMap ℚ A t := ⟨_, rfl⟩
  have hw : σ w = w := by
    rw [hwdef]
    rw [map_sub]
    change σ (σ γ * γ) - σ (algebraMap ℚ A t) = _
    rw [σ.apply_mul, σ.apply_apply, σ.apply_algebraMap]
  have e : ∀ y z : A, σ (γ * y) * (γ * z) - t • (σ y * z) = σ y * w * z := fun y z => by
    rw [σ.apply_mul, hwdef, mul_sub, sub_mul, Algebra.algebraMap_eq_smul_one, mul_smul_comm,
      mul_one, smul_mul_assoc, mul_assoc, mul_assoc, mul_assoc]
  have key : σ.traceForm (γ * 1) (γ * w) - t * σ.traceForm 1 w =
      Langlands.Algebra.regularTrace ℚ A (σ 1 * w * w) +
        Langlands.Algebra.regularTrace ℚ A (σ w * w * 1) := by
    rw [traceForm_apply, traceForm_apply, ← e 1 w, ← e w 1, map_sub, map_sub, map_smul,
      map_smul, smul_eq_mul, smul_eq_mul]
    ring
  rw [h, sub_self, σ.apply_one, one_mul, mul_one] at key
  have hww : σ w * w = w * w := by rw [hw]
  have hT : σ.traceForm w w = 0 := by
    rw [traceForm_apply, hww]
    rw [hww] at key
    linarith
  by_contra hne
  have hpos' := traceForm_self_pos σ hpos (a := w) (by rw [hwdef]; exact sub_ne_zero.2 hne)
  linarith

/-- Matrix form of `apply_mul_self_eq_of_traceForm`: `Γᵀ G Γ = t G` for the matrix `Γ` of left
multiplication by `γ` forces `σ(γ) γ = t`. -/
theorem apply_mul_self_eq_of_gram (σ : AlgebraInvolution ℚ A)
    (hpos : (σ.baseChange ℝ).IsPositive) (b : Basis ι ℚ A) {γ : A} {t : ℚ}
    (h : (Algebra.leftMulMatrix b γ)ᵀ * LinearMap.BilinForm.toMatrix b σ.traceForm *
        Algebra.leftMulMatrix b γ = t • LinearMap.BilinForm.toMatrix b σ.traceForm) :
    σ γ * γ = algebraMap ℚ A t := by
  rw [Algebra.leftMulMatrix_apply, ← LinearMap.BilinForm.toMatrix_comp, ← map_smul] at h
  have h' := (LinearMap.BilinForm.toMatrix b).injective h
  exact apply_mul_self_eq_of_traceForm σ hpos fun y z => LinearMap.congr_fun₂ h' y z

end Positive

end Langlands.Shimura.AlgebraInvolution
