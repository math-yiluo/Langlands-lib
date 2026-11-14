import Langlands.GroupScheme.EvenOrthogonalForm.Similitude
import Langlands.GroupScheme.SymplecticInnerForm.GaloisInvolution
import Mathlib.RingTheory.Trace.Basic

/-! # The algebra with involution descended along a similitude cocycle

Let `N/K` be a finite Galois extension and let `g : Gal(N/K) → GL_{2n}(N)` be a family of
similitudes of the split hyperbolic quadratic form whose twisted action
`θ_γ(x) = g_γ⁻¹ γ(x) g_γ` on `M_{2n}(N)` is an action of `Gal(N/K)`. This module introduces

* the semilinear Galois action `twistedAction g hcoc` given by `θ`, so that its fixed
  algebra is a central simple `K`-algebra (the Galois descent of `M_{2n}(N)`);
* the descended orthogonal involution `descendedInvolution`, the restriction of
  `τ₀ x = J xᵀ J` to the fixed algebra, and the compatibility of the descent chart with `τ₀`;
* a base point `basePoint` of the fixed algebra with `a₀ + τ a₀ = 1` and
  `a₀ - p ∈ {y - τ₀ y}`, where `p = [[1, 0], [0, 0]]`, obtained by Galois averaging
  `c • p` for an element `c` of trace one.
-/

noncomputable section

universe u

open Matrix
open scoped Matrix TensorProduct

namespace Langlands.GroupScheme.EvenOrthogonalForm

open OrthogonalMatrix Quaternionic Langlands.CentralSimple

variable {K N : Type u} [Field K] [Field N] [Algebra K N] {n : ℕ}
  (g : (N ≃ₐ[K] N) → GL (Fin n ⊕ Fin n) N)

/-! ### The twisted action -/

/-- The twisted action `x ↦ g_γ⁻¹ γ(x) g_γ` of `γ` on matrices. -/
def twistMatrix (γ : N ≃ₐ[K] N) (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N :=
  (↑(g γ)⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) * x.map γ *
    (g γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N)

theorem map_galois_mul (γ : N ≃ₐ[K] N) (x y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) :
    (x * y).map γ = x.map γ * y.map γ :=
  Matrix.map_mul (f := (γ : N →+* N))

/-- Undoing the conjugation in the twisted action recovers the entrywise action. -/
theorem mul_twistMatrix_mul (γ : N ≃ₐ[K] N) (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) :
    (g γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) * twistMatrix g γ x *
        (↑(g γ)⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) = x.map γ := by
  simp only [twistMatrix, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one,
    Units.mul_inv_cancel_left]

theorem twistMatrix_injective (γ : N ≃ₐ[K] N) : Function.Injective (twistMatrix g γ) := by
  intro x y h
  have h1 : x.map γ = y.map γ := by
    rw [← mul_twistMatrix_mul g γ x, ← mul_twistMatrix_mul g γ y, h]
  ext i j
  exact γ.injective (congrFun (congrFun h1 i) j)

/-- The twisted action of `γ` as a ring endomorphism of the matrix algebra. -/
def twistRingHom (γ : N ≃ₐ[K] N) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N →+* Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N where
  toFun := twistMatrix g γ
  map_one' := by
    rw [twistMatrix, Matrix.map_one _ (map_zero γ) (map_one γ), Matrix.mul_one, Units.inv_mul]
  map_mul' x y := by
    rw [twistMatrix, twistMatrix, twistMatrix, map_galois_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (g γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N), Units.mul_inv,
      Matrix.one_mul]
  map_zero' := by
    rw [twistMatrix, Matrix.map_zero _ (map_zero γ), Matrix.mul_zero, Matrix.zero_mul]
  map_add' x y := by
    rw [twistMatrix, twistMatrix, twistMatrix, Matrix.map_add _ (map_add γ), Matrix.mul_add,
      Matrix.add_mul]

theorem twistRingHom_apply (γ : N ≃ₐ[K] N) (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) :
    twistRingHom g γ x = twistMatrix g γ x :=
  rfl

theorem twistMatrix_algebraMap (γ : N ≃ₐ[K] N) (l : N) :
    twistMatrix g γ (algebraMap N (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) l) =
      algebraMap N (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) (γ l) := by
  have h : (algebraMap N (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) l).map γ =
      algebraMap N (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) (γ l) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.algebraMap_matrix_apply]
    split_ifs <;> simp
  rw [twistMatrix, h, Matrix.mul_assoc, Algebra.commutes, ← Matrix.mul_assoc, Units.inv_mul,
    Matrix.one_mul]

variable (hcoc : ∀ γ δ x, twistMatrix g γ (twistMatrix g δ x) = twistMatrix g (γ * δ) x)

/-- The twisted Galois action `γ · x = g_γ⁻¹ γ(x) g_γ` on `M_{2n}(N)`. -/
def twistedAction :
    SemilinearGaloisAction K N (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) where
  act := twistRingHom g
  act_algebraMap := twistMatrix_algebraMap g
  act_one x := by
    apply twistMatrix_injective g 1
    have h := hcoc 1 1 x
    rw [mul_one] at h
    exact h
  act_mul γ δ x := (hcoc γ δ x).symm

theorem twistedAction_act (γ : N ≃ₐ[K] N) (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) :
    (twistedAction g hcoc).act γ x = twistMatrix g γ x :=
  rfl

/-- A fixed element `a` satisfies `γ(a) = g_γ a g_γ⁻¹`. -/
theorem map_galois_fixed (γ : N ≃ₐ[K] N) (a : (twistedAction g hcoc).fixed) :
    (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N).map γ =
      (g γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) * a *
        (↑(g γ)⁻¹ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) := by
  rw [← mul_twistMatrix_mul g γ]
  congr 2
  exact (twistedAction g hcoc).act_fixed γ a

variable [FiniteDimensional K N] [IsGalois K N]

instance : FiniteDimensional K (twistedAction g hcoc).fixed :=
  (twistedAction g hcoc).finiteDimensional_fixed

instance [NeZero n] : Algebra.IsCentral K (twistedAction g hcoc).fixed :=
  (twistedAction g hcoc).isCentral_fixed

instance [NeZero n] : IsSimpleRing (twistedAction g hcoc).fixed :=
  (twistedAction g hcoc).isSimpleRing_fixed

/-! ### The descended involution -/

omit [FiniteDimensional K N] [IsGalois K N] in
variable {g} in
/-- For similitudes, the twisted action commutes with `τ₀ x = J xᵀ J`. -/
theorem twistMatrix_orthogonalInvolution
    (hsim : ∀ γ, ∃ μ : Nˣ, IsAlt ((g γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) *
      formMatrix (Fin n) N * (g γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N)ᵀ -
        (μ : N) • formMatrix (Fin n) N))
    (γ : N ≃ₐ[K] N) (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) :
    twistMatrix g γ (orthogonalInvolution N (Fin n) x) =
      orthogonalInvolution N (Fin n) (twistMatrix g γ x) := by
  obtain ⟨μ, hμ⟩ := hsim γ
  have hmap : (orthogonalInvolution N (Fin n) x).map γ =
      orthogonalInvolution N (Fin n) (x.map γ) :=
    orthogonalInvolution_map (γ : N →+* N) x
  rw [twistMatrix, twistMatrix, hmap,
    orthogonalInvolution_conj_of_similitude (Units.inv_mul (g γ)) (Units.inv_mul μ)
      (similitude_polar hμ)]

variable (hsim : ∀ γ, ∃ μ : Nˣ, IsAlt ((g γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) *
  formMatrix (Fin n) N * (g γ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N)ᵀ -
    (μ : N) • formMatrix (Fin n) N))

/-- The involution of the fixed algebra induced by `τ₀ x = J xᵀ J`. -/
def descendedInvolution : FirstKindInvolution K (twistedAction g hcoc).fixed :=
  (twistedAction g hcoc).fixedInvolution (orthogonalInvolution N (Fin n))
    (twistMatrix_orthogonalInvolution hsim)

omit [FiniteDimensional K N] [IsGalois K N] in
theorem coe_descendedInvolution (a : (twistedAction g hcoc).fixed) :
    (descendedInvolution g hcoc hsim a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) =
      orthogonalInvolution N (Fin n) a :=
  rfl

/-- The descent chart carries the extended descended involution to `τ₀`. -/
theorem descentEquiv_descendedInvolution (x : N ⊗[K] (twistedAction g hcoc).fixed) :
    (twistedAction g hcoc).descentEquiv ((descendedInvolution g hcoc hsim).baseChange N x) =
      orthogonalInvolution N (Fin n) ((twistedAction g hcoc).descentEquiv x) :=
  SemilinearGaloisAction.descentEquiv_fixedInvolution _ _ _ x

/-- The descent chart intertwines the descended involution with the adjoint involution of the
polar matrix `J`. -/
theorem descentEquiv_descendedInvolution_mul_polar (x : N ⊗[K] (twistedAction g hcoc).fixed) :
    (twistedAction g hcoc).descentEquiv ((descendedInvolution g hcoc hsim).baseChange N x) *
        polarMatrix (Fin n) N =
      polarMatrix (Fin n) N * ((twistedAction g hcoc).descentEquiv x)ᵀ := by
  rw [descentEquiv_descendedInvolution, orthogonalInvolution_mul_polar]

/-! ### The base point -/

variable (K N) in
theorem exists_trace_eq_one : ∃ c : N, Algebra.trace K N c = 1 := by
  obtain ⟨c, hc⟩ : ∃ c, Algebra.trace K N c ≠ 0 := by
    by_contra h
    push Not at h
    exact Algebra.trace_ne_zero K N (LinearMap.ext h)
  exact ⟨(Algebra.trace K N c)⁻¹ • c, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hc]⟩

variable (K N) in
/-- A chosen element of trace one. -/
def traceOneElement : N :=
  (exists_trace_eq_one K N).choose

variable (K N) in
theorem sum_galois_traceOneElement : ∑ γ : N ≃ₐ[K] N, γ (traceOneElement K N) = 1 := by
  rw [← trace_eq_sum_automorphisms, traceOneElement,
    (exists_trace_eq_one K N).choose_spec, map_one]

/-- The base point `a₀ = ∑_γ θ_γ(c • p)` of the fixed algebra, for an element `c` of trace one
and the projection `p = [[1, 0], [0, 0]]`. -/
def basePoint : (twistedAction g hcoc).fixed :=
  (twistedAction g hcoc).trace (traceOneElement K N • leftProjection N (Fin n))

omit [FiniteDimensional K N] [IsGalois K N] in
theorem twistMatrix_smul (γ : N ≃ₐ[K] N) (c : N)
    (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) :
    twistMatrix g γ (c • x) = γ c • twistMatrix g γ x := by
  rw [Algebra.smul_def, Algebra.smul_def, ← twistRingHom_apply, _root_.map_mul,
    twistRingHom_apply, twistMatrix_algebraMap, twistRingHom_apply]

theorem coe_basePoint :
    (basePoint g hcoc : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) =
      ∑ γ : N ≃ₐ[K] N,
        γ (traceOneElement K N) • twistMatrix g γ (leftProjection N (Fin n)) := by
  rw [basePoint, SemilinearGaloisAction.coe_trace]
  refine Finset.sum_congr rfl fun γ _ => ?_
  exact twistMatrix_smul g γ _ _

omit [FiniteDimensional K N] [IsGalois K N] in
include hsim in
variable {g} in
theorem twistMatrix_leftProjection_sub_mem (γ : N ≃ₐ[K] N) :
    twistMatrix g γ (leftProjection N (Fin n)) - leftProjection N (Fin n) ∈
      (orthogonalInvolution N (Fin n)).alternatingSubspace := by
  obtain ⟨μ, hμ⟩ := hsim γ
  have hmap : (leftProjection N (Fin n)).map γ = leftProjection N (Fin n) :=
    leftProjection_map (γ : N →+* N)
  rw [twistMatrix, hmap]
  exact conj_leftProjection_sub_mem (Units.inv_mul (g γ)) hμ

include hsim in
/-- The base point is congruent to `p = [[1, 0], [0, 0]]` modulo the alternating elements
of `τ₀`. -/
theorem basePoint_sub_mem :
    (basePoint g hcoc : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) - leftProjection N (Fin n) ∈
      (orthogonalInvolution N (Fin n)).alternatingSubspace := by
  have h : (basePoint g hcoc : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) -
      leftProjection N (Fin n) = ∑ γ : N ≃ₐ[K] N, γ (traceOneElement K N) •
        (twistMatrix g γ (leftProjection N (Fin n)) - leftProjection N (Fin n)) := by
    rw [coe_basePoint]
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, sum_galois_traceOneElement, one_smul]
  rw [h]
  exact Submodule.sum_mem _ fun γ _ =>
    Submodule.smul_mem _ _ (twistMatrix_leftProjection_sub_mem hsim γ)

/-- The base point satisfies `a₀ + τ a₀ = 1`. -/
theorem basePoint_add_descendedInvolution :
    basePoint g hcoc + descendedInvolution g hcoc hsim (basePoint g hcoc) = 1 := by
  apply Subtype.ext
  rw [Subalgebra.coe_add, coe_descendedInvolution, Subalgebra.coe_one, coe_basePoint,
    FirstKindInvolution.map_sum, ← Finset.sum_add_distrib]
  have h : ∀ γ : N ≃ₐ[K] N,
      γ (traceOneElement K N) • twistMatrix g γ (leftProjection N (Fin n)) +
        orthogonalInvolution N (Fin n)
          (γ (traceOneElement K N) • twistMatrix g γ (leftProjection N (Fin n))) =
      algebraMap N (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) N) (γ (traceOneElement K N)) := by
    intro γ
    rw [FirstKindInvolution.map_smul, ← twistMatrix_orthogonalInvolution hsim, ← smul_add,
      ← twistRingHom_apply, ← twistRingHom_apply, ← _root_.map_add,
      leftProjection_add_orthogonalInvolution, _root_.map_one, ← Algebra.algebraMap_eq_smul_one]
  simp_rw [h]
  rw [← _root_.map_sum, sum_galois_traceOneElement, _root_.map_one]

end Langlands.GroupScheme.EvenOrthogonalForm
