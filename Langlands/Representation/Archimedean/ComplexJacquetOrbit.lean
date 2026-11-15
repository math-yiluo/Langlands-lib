import Langlands.Representation.Archimedean.ComplexJacquetTorus

/-!
# Smoothness of matrix coefficients on skew-Hermitian matrices

Let `(ρ, π)` be a `(𝔤𝔩_n(ℂ), U(n))`-module on `V`, `w ∈ V` and `μ` a linear functional on `V`.
The matrix coefficient `Y ↦ μ(ρ(exp Y) w)` on skew-Hermitian matrices `Y` is the restriction of
a `C^∞` function on all matrices (`IsComplexGKModule.exists_contDiff_coeff`).

The proof uses that the orbit span `W` of `w` is finite-dimensional. In a basis `e` of `W`,
with coordinate functionals `λ_i` extended to `V`, the matrices
`M(k)_ij = λ_i(ρ(k) e_j)` form a homomorphism of `U(n)` (`orbitMatrix_mul`). Along the
one-parameter subgroup `t ↦ exp(tY)` the curve clause of `IsComplexGKModule` gives
`M'(0) = A(Y)` with `A(Y)_ij = λ_i(π(1 ⊗ Y) e_j)`, so `M'(t) = M(t) A(Y)` and
`M(exp Y) = exp(A(Y))` (`orbitMatrix_skewExp`). The map `Y ↦ A(Y)` is real linear on all
matrices, so `Y ↦ ∑ λ_j(w) μ(e_i) exp(A(Y))_ij` is `C^∞`.
-/

noncomputable section

open scoped TensorProduct Matrix Matrix.Norms.Operator ContDiff

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

-- As in `GeneralLinear`: the operator norm on matrices needs reduction through the
-- normed-ring instances.
set_option backward.isDefEq.respectTransparency false

universe uV

/-! ## The exponential is smooth -/

theorem contDiff_matrix_exp (m : ℕ) :
    ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin m) (Fin m) ℂ → Matrix (Fin m) (Fin m) ℂ) :=
  contDiff_iff_contDiffAt.mpr fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt

/-- Solution of `M' = M A` with `M(0) = 1`: `M(t) = exp(tA)`. -/
theorem eq_exp_of_hasDerivAt_mul {m : ℕ} {M : ℝ → Matrix (Fin m) (Fin m) ℂ}
    {A : Matrix (Fin m) (Fin m) ℂ} (h : ∀ t, HasDerivAt M (M t * A) t) (h0 : M 0 = 1)
    (t : ℝ) : M t = NormedSpace.exp (t • A) := by
  set P : ℝ → Matrix (Fin m) (Fin m) ℂ := fun s => M s * NormedSpace.exp (s • -A) with hP
  have hd : ∀ s, HasDerivAt P 0 s := by
    intro s
    have h1 := (h s).mul (hasDerivAt_exp_smul_const (-A) s)
    have hc : Commute A (NormedSpace.exp (s • -A)) :=
      (((Commute.refl A).neg_right).smul_right s).exp_right
    refine h1.congr_deriv ?_
    rw [mul_assoc, hc.eq, mul_neg, mul_neg, add_neg_cancel]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simp only [hP, h0, zero_smul, NormedSpace.exp_zero, mul_one] at hconst
  have hinv : NormedSpace.exp (t • -A) * NormedSpace.exp (t • A) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl A).neg_left.smul_left t).smul_right t),
      smul_neg, neg_add_cancel, NormedSpace.exp_zero]
  calc M t = M t * NormedSpace.exp (t • -A) * NormedSpace.exp (t • A) := by
        rw [mul_assoc, hinv, mul_one]
    _ = NormedSpace.exp (t • A) := by rw [hconst, one_mul]

/-! ## The orbit matrices -/

section Orbit

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}

/-- A basis of the orbit span of `w` together with coordinate functionals on `V`. -/
structure OrbitFrame (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V) (w : V) where
  /-- The dimension of the orbit span. -/
  dim : ℕ
  /-- The basis vectors. -/
  vec : Fin dim → V
  /-- The coordinate functionals. -/
  coord : Fin dim → V →ₗ[ℂ] ℂ
  vec_mem : ∀ j, vec j ∈ FiniteVectors.orbitSpan ρ w
  coord_vec : ∀ i j, coord i (vec j) = if i = j then 1 else 0
  sum_coord : ∀ x ∈ FiniteVectors.orbitSpan ρ w, ∑ i, coord i x • vec i = x

/-- A finite vector has an orbit frame. -/
theorem exists_orbitFrame (w : V) (hw : FiniteVectors.IsFiniteVector ρ w) :
    Nonempty (OrbitFrame ρ w) := by
  classical
  let W := FiniteVectors.orbitSpan ρ w
  have : Module.Finite ℂ W := hw
  let e := Module.finBasis ℂ W
  have hext : ∀ i, ∃ g : V →ₗ[ℂ] ℂ, g.comp W.subtype = e.coord i :=
    fun i => LinearMap.exists_extend (e.coord i)
  choose g hg using hext
  have hgx : ∀ i (x : W), g i x = e.repr x i := by
    intro i x
    have := congrArg (fun f : W →ₗ[ℂ] ℂ => f x) (hg i)
    simpa using this
  refine ⟨⟨Module.finrank ℂ W, fun j => (e j : V), g, fun j => (e j).2, ?_, ?_⟩⟩
  · intro i j
    rw [hgx i (e j), Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  · intro x hx
    have h2 : ∑ i, ((e.repr ⟨x, hx⟩ i • e i : W) : V) = x := by
      rw [← Submodule.coe_sum, e.sum_repr]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h2
    rw [Submodule.coe_smul, show g i x = e.repr ⟨x, hx⟩ i from hgx i ⟨x, hx⟩]

variable {w : V}

/-- The matrix of `ρ(k)` on the orbit span in an orbit frame. -/
def orbitMatrix (fr : OrbitFrame ρ w) (k : Matrix.unitaryGroup (Fin n) ℂ) :
    Matrix (Fin fr.dim) (Fin fr.dim) ℂ :=
  Matrix.of fun i j => fr.coord i (ρ k (fr.vec j))

@[simp]
theorem orbitMatrix_apply (fr : OrbitFrame ρ w) (k : Matrix.unitaryGroup (Fin n) ℂ)
    (i j : Fin fr.dim) : orbitMatrix fr k i j = fr.coord i (ρ k (fr.vec j)) :=
  rfl

theorem OrbitFrame.rho_vec_mem (fr : OrbitFrame ρ w) (k : Matrix.unitaryGroup (Fin n) ℂ)
    (j : Fin fr.dim) : ρ k (fr.vec j) ∈ FiniteVectors.orbitSpan ρ w :=
  (FiniteVectors.orbitSubrepresentation ρ w).apply_mem_toSubmodule k (fr.vec_mem j)

theorem OrbitFrame.rho_vec (fr : OrbitFrame ρ w) (k : Matrix.unitaryGroup (Fin n) ℂ)
    (j : Fin fr.dim) : ρ k (fr.vec j) = ∑ i, orbitMatrix fr k i j • fr.vec i :=
  (fr.sum_coord _ (fr.rho_vec_mem k j)).symm

theorem orbitMatrix_one (fr : OrbitFrame ρ w) : orbitMatrix fr 1 = 1 := by
  ext i j
  rw [orbitMatrix_apply, map_one, Module.End.one_apply, fr.coord_vec, Matrix.one_apply]

theorem orbitMatrix_mul (fr : OrbitFrame ρ w) (k k' : Matrix.unitaryGroup (Fin n) ℂ) :
    orbitMatrix fr (k * k') = orbitMatrix fr k * orbitMatrix fr k' := by
  ext i j
  rw [Matrix.mul_apply, orbitMatrix_apply, map_mul, Module.End.mul_apply, fr.rho_vec k' j,
    map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, map_smul, smul_eq_mul, mul_comm]
  rfl

/-- `μ(ρ(k) w) = ∑ᵢⱼ λ_j(w) μ(e_i) M(k)_ij`. -/
theorem OrbitFrame.apply_rho (fr : OrbitFrame ρ w) (μ : V →ₗ[ℂ] ℂ)
    (k : Matrix.unitaryGroup (Fin n) ℂ) :
    μ (ρ k w) = ∑ i, ∑ j, fr.coord j w * μ (fr.vec i) * orbitMatrix fr k i j := by
  have hw : w = ∑ j, fr.coord j w • fr.vec j :=
    (fr.sum_coord w (FiniteVectors.self_mem_orbitSpan ρ w)).symm
  conv_lhs => rw [hw]
  rw [map_sum, map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul, fr.rho_vec k j, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  ring

/-- The infinitesimal matrix `A(Y)_ij = λ_i(π(1 ⊗ Y) e_j)`, real linear in `Y`. -/
def orbitLie (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (fr : OrbitFrame ρ w) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin fr.dim) (Fin fr.dim) ℂ where
  toFun Y := Matrix.of fun i j => fr.coord i (π (1 ⊗ₜ Y) (fr.vec j))
  map_add' Y Y' := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, lie_one_tmul_add, map_add]
  map_smul' r Y := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, lie_one_tmul_real_smul, map_smul,
      RingHom.id_apply, smul_eq_mul, Complex.real_smul]

theorem orbitLie_apply (fr : OrbitFrame ρ w) (Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin fr.dim) :
    orbitLie π fr Y i j = fr.coord i (π (1 ⊗ₜ Y) (fr.vec j)) :=
  rfl

/-- Along `t ↦ exp(tY)` the orbit matrix is `exp(t A(Y))`. -/
theorem orbitMatrix_skewExp (hgk : IsComplexGKModule n ρ π) (fr : OrbitFrame ρ w)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : star Y = -Y) (t : ℝ) :
    orbitMatrix fr (skewExp (t • Y) (star_real_smul_of_skew hY t)) =
      NormedSpace.exp (t • orbitLie π fr Y) := by
  set M : ℝ → Matrix (Fin fr.dim) (Fin fr.dim) ℂ :=
    fun s => orbitMatrix fr (skewExp (s • Y) (star_real_smul_of_skew hY s)) with hM
  have hM0 : M 0 = 1 := by
    simp only [hM, skewExp_zero_smul hY, orbitMatrix_one]
  have hd0 : HasDerivAt M (orbitLie π fr Y) 0 := by
    apply hasDerivAt_matrix_of_entries
    intro i j
    exact hgk.2.2.1 _ Y (skewExp_zero_smul hY) (hasDerivAt_skewExp_entry hY) (fr.vec j)
      (fr.coord i)
  have hd : ∀ s, HasDerivAt M (M s * orbitLie π fr Y) s := by
    intro s
    have h1 : HasDerivAt (fun t => M (t - s)) (orbitLie π fr Y) s := by
      have hd0' : HasDerivAt M (orbitLie π fr Y) (s - s) := by rwa [sub_self]
      exact hd0'.comp_sub_const s s
    have h2 := h1.const_mul (M s)
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    change M t = M s * M (t - s)
    simp only [hM]
    rw [← orbitMatrix_mul, ← skewExp_add_smul hY, add_sub_cancel]
  exact eq_exp_of_hasDerivAt_mul hd hM0 t

/-- **Smooth matrix coefficients.** For `w ∈ V` and a linear functional `μ`, there is a `C^∞`
function `G` on all matrices with `G(Y) = μ(ρ(exp Y) w)` for skew-Hermitian `Y`. -/
theorem IsComplexGKModule.exists_contDiff_coeff (hgk : IsComplexGKModule n ρ π) (w : V)
    (μ : V →ₗ[ℂ] ℂ) :
    ∃ G : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ G ∧
      ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (hY : star Y = -Y), G Y = μ (ρ (skewExp Y hY) w) := by
  obtain ⟨fr⟩ := exists_orbitFrame (ρ := ρ) w (hgk.1 w)
  set A := orbitLie π fr with hA
  refine ⟨fun Y => ∑ i, ∑ j, fr.coord j w * μ (fr.vec i) *
    (NormedSpace.exp (A Y)) i j, ?_, ?_⟩
  · have hAc : ContDiff ℝ ∞ (fun Y => A Y) :=
      (LinearMap.toContinuousLinearMap A).contDiff
    have hE : ContDiff ℝ ∞ (fun Y => NormedSpace.exp (A Y)) :=
      (contDiff_matrix_exp fr.dim).comp hAc
    refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
    have hentry : ContDiff ℝ ∞ (fun Y => (NormedSpace.exp (A Y)) i j) :=
      (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).contDiff.comp hE
    exact contDiff_const.mul hentry
  · intro Y hY
    have hk : skewExp Y hY = skewExp ((1 : ℝ) • Y) (star_real_smul_of_skew hY 1) :=
      Subtype.ext (by simp)
    rw [fr.apply_rho μ, hk, orbitMatrix_skewExp hgk fr hY, one_smul]

end Orbit

end Langlands.Archimedean
