import Langlands.Representation.Archimedean.FiniteFunctionSpaces
import Langlands.Representation.Archimedean.PrincipalSeriesStability

/-!
# Functions polynomial along a root subgroup

For `i ≠ j` in `Fin n`, `rootUnit hij z = 1 + z E_{j,i}` is the root element of `GL_n(ℂ)`
(lower unipotent when `i < j`). `IsBlockPoly hij p q F` says that for every `g` the function
`z ↦ F(rootUnit hij z · g)`
is a polynomial in `z` and `z̄` of degree `< p` in `z` and `< q` in `z̄` (it lies in
`bidegLT p q`). `isBlockPoly_rightDerivative`: right derivatives of smooth functions on `GL_n(ℂ)`
preserve this property, since left and right translations commute and derivatives of
families in the finite-dimensional space `bidegLT p q` stay in it.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator ComplexConjugate ContDiff Manifold

set_option autoImplicit false

namespace Langlands.Archimedean.BlockPolynomial

open Langlands.GeneralLinear

set_option backward.isDefEq.respectTransparency false

/-! ## Polynomials of bounded bidegree in `z` and `z̄` -/

/-- The span of `z^a z̄^b`, `a < p`, `b < q`. -/
def bidegLT (p q : ℕ) : Submodule ℂ (ℂ → ℂ) :=
  Submodule.span ℂ (Set.range fun ab : Fin p × Fin q =>
    fun z : ℂ => z ^ (ab.1 : ℕ) * conj z ^ (ab.2 : ℕ))

instance bidegLT_finiteDimensional (p q : ℕ) : FiniteDimensional ℂ (bidegLT p q) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

theorem bidegLT_mono {p q p' q' : ℕ} (hp : p ≤ p') (hq : q ≤ q') :
    bidegLT p q ≤ bidegLT p' q' := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨ab, rfl⟩
  exact Submodule.subset_span ⟨(⟨ab.1, ab.1.2.trans_le hp⟩, ⟨ab.2, ab.2.2.trans_le hq⟩), rfl⟩

theorem const_mem_bidegLT (c : ℂ) : (fun _ : ℂ => c) ∈ bidegLT 1 1 := by
  have : (fun _ : ℂ => c) = c • fun z : ℂ => z ^ ((0 : Fin 1) : ℕ) * conj z ^ ((0 : Fin 1) : ℕ) := by
    funext z; simp
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(0, 0), rfl⟩)

/-- Multiplying by an affine function of `z` raises the `z`-degree by one. -/
theorem affine_mul_mem {p q : ℕ} {f : ℂ → ℂ} (hf : f ∈ bidegLT p q) (c₀ c₁ : ℂ) :
    (fun z => (c₀ + c₁ * z) * f z) ∈ bidegLT (p + 1) q := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ab, rfl⟩ := hf
    have : (fun z => (c₀ + c₁ * z) * (z ^ (ab.1 : ℕ) * conj z ^ (ab.2 : ℕ))) =
        c₀ • (fun z : ℂ => z ^ (ab.1 : ℕ) * conj z ^ (ab.2 : ℕ)) +
          c₁ • fun z : ℂ => z ^ ((ab.1 : ℕ) + 1) * conj z ^ (ab.2 : ℕ) := by
      funext z; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span ⟨(⟨ab.1, by omega⟩, ab.2), rfl⟩
    · exact Submodule.subset_span ⟨(⟨(ab.1 : ℕ) + 1, by omega⟩, ab.2), rfl⟩
  | zero =>
    have : (fun z => (c₀ + c₁ * z) * (0 : ℂ → ℂ) z) = 0 := by funext z; simp
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (fun z => (c₀ + c₁ * z) * (x + y) z) =
        (fun z => (c₀ + c₁ * z) * x z) + fun z => (c₀ + c₁ * z) * y z := by
      funext z; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    have : (fun z => (c₀ + c₁ * z) * (r • x) z) = r • fun z => (c₀ + c₁ * z) * x z := by
      funext z; simp [mul_left_comm]
    rw [this]; exact Submodule.smul_mem _ r hx

/-- Multiplying by the conjugate of an affine function raises the `z̄`-degree by one. -/
theorem conj_affine_mul_mem {p q : ℕ} {f : ℂ → ℂ} (hf : f ∈ bidegLT p q) (c₀ c₁ : ℂ) :
    (fun z => conj (c₀ + c₁ * z) * f z) ∈ bidegLT p (q + 1) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ab, rfl⟩ := hf
    have : (fun z => conj (c₀ + c₁ * z) * (z ^ (ab.1 : ℕ) * conj z ^ (ab.2 : ℕ))) =
        conj c₀ • (fun z : ℂ => z ^ (ab.1 : ℕ) * conj z ^ (ab.2 : ℕ)) +
          conj c₁ • fun z : ℂ => z ^ (ab.1 : ℕ) * conj z ^ ((ab.2 : ℕ) + 1) := by
      funext z; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]; ring
    rw [this]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span ⟨(ab.1, ⟨ab.2, by omega⟩), rfl⟩
    · exact Submodule.subset_span ⟨(ab.1, ⟨(ab.2 : ℕ) + 1, by omega⟩), rfl⟩
  | zero =>
    have : (fun z => conj (c₀ + c₁ * z) * (0 : ℂ → ℂ) z) = 0 := by funext z; simp
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (fun z => conj (c₀ + c₁ * z) * (x + y) z) =
        (fun z => conj (c₀ + c₁ * z) * x z) + fun z => conj (c₀ + c₁ * z) * y z := by
      funext z; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    have : (fun z => conj (c₀ + c₁ * z) * (r • x) z) = r • fun z => conj (c₀ + c₁ * z) * x z := by
      funext z; simp [mul_left_comm]
    rw [this]; exact Submodule.smul_mem _ r hx

/-! ## The root element and block polynomiality -/

variable {n : ℕ}

/-- The matrix `1 + z E_{j,i}`. -/
def rootMatrix (i : Fin n) (j : Fin n) (z : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + Matrix.single j i z

theorem rootMatrix_mul_neg {i j : Fin n} (hij : i ≠ j) (z : ℂ) :
    rootMatrix i j z * rootMatrix i j (-z) = 1 := by
  have h0 : Matrix.single j i z * Matrix.single j i (-z) = 0 :=
    Matrix.single_mul_single_of_ne (h := hij) ..
  unfold rootMatrix
  rw [add_mul, mul_add, mul_add]
  erw [h0]
  have hn : Matrix.single j i (-z) = -Matrix.single j i z := by
    ext a b; simp only [Matrix.single_apply, Matrix.neg_apply]; split_ifs <;> simp
  simp only [mul_one, one_mul, add_zero, hn]
  abel

/-- The root element `1 + z E_{j,i}` (for `i ≠ j`) as a unit. -/
def rootUnit {i j : Fin n} (hij : i ≠ j) (z : ℂ) : Langlands.GeneralLinear n ℂ :=
  ⟨rootMatrix i j z, rootMatrix i j (-z), rootMatrix_mul_neg hij z, by
    simpa using rootMatrix_mul_neg hij (-z)⟩

@[simp]
theorem rootUnit_val {i j : Fin n} (hij : i ≠ j) (z : ℂ) :
    ((rootUnit hij z : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      rootMatrix i j z := rfl

/-- `F (rootUnit z · g)` is a polynomial of bidegree `< (p, q)` in `(z, z̄)` for every `g`. -/
def IsBlockPoly {i j : Fin n} (hij : i ≠ j) (p q : ℕ) (F : Langlands.GeneralLinear n ℂ → ℂ) :
    Prop :=
  ∀ g : Langlands.GeneralLinear n ℂ, (fun z => F (rootUnit hij z * g)) ∈ bidegLT p q

/-- Block-polynomial functions form a subspace. -/
def blockPolySubmodule {i j : Fin n} (hij : i ≠ j) (p q : ℕ) :
    Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) where
  carrier := {F | IsBlockPoly hij p q F}
  add_mem' {F G} hF hG g := by
    have : (fun z => (F + G) (rootUnit hij z * g)) =
        (fun z => F (rootUnit hij z * g)) + fun z => G (rootUnit hij z * g) := rfl
    rw [this]; exact Submodule.add_mem _ (hF g) (hG g)
  zero_mem' g := by
    have : (fun z => (0 : Langlands.GeneralLinear n ℂ → ℂ) (rootUnit hij z * g)) = 0 := rfl
    rw [this]; exact Submodule.zero_mem _
  smul_mem' c F hF g := by
    have : (fun z => (c • F) (rootUnit hij z * g)) = c • fun z => F (rootUnit hij z * g) := rfl
    rw [this]; exact Submodule.smul_mem _ c (hF g)

theorem isBlockPoly_rightTranslation {i j : Fin n} (hij : i ≠ j) {p q : ℕ}
    {F : Langlands.GeneralLinear n ℂ → ℂ} (hF : IsBlockPoly hij p q F)
    (k : Langlands.GeneralLinear n ℂ) :
    IsBlockPoly hij p q (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k F) := by
  intro g
  have : (fun z => Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k F
      (rootUnit hij z * g)) = fun z => F (rootUnit hij z * (g * k)) := by
    funext z
    change F (rootUnit hij z * g * k) = F (rootUnit hij z * (g * k))
    rw [mul_assoc]
  rw [this]
  exact hF (g * k)

/-- **Right derivatives preserve block polynomiality** of smooth functions. -/
theorem isBlockPoly_rightDerivative {i j : Fin n} (hij : i ≠ j) {p q : ℕ}
    {F : Langlands.GeneralLinear n ℂ → ℂ} (hFs : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ F)
    (hF : IsBlockPoly hij p q F) (X : Matrix (Fin n) (Fin n) ℂ) :
    IsBlockPoly hij p q (rightDerivative (matrixModel ℂ n) X F) := by
  intro g
  set Φ := unitsExtension F
  let M : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t =>
    (g : Matrix (Fin n) (Fin n) ℂ) + t • ((g : Matrix (Fin n) (Fin n) ℂ) * X)
  let Fam : ℝ → ℂ → ℂ := fun t z => Φ (rootMatrix i j z * M t)
  have hFam : ∀ t, Fam t ∈ bidegLT p q := by
    intro t
    by_cases ht : IsUnit (M t)
    · have : Fam t = fun z => F (rootUnit hij z * ht.unit) := by
        funext z
        simp only [Fam, Φ]
        rw [show rootMatrix i j z * M t =
            ((rootUnit hij z * ht.unit : Langlands.GeneralLinear n ℂ) :
              Matrix (Fin n) (Fin n) ℂ) by simp, unitsExtension_val]
      rw [this]
      exact hF ht.unit
    · have : Fam t = 0 := by
        funext z
        simp only [Fam, Φ, Pi.zero_apply]
        refine unitsExtension_of_not_isUnit _ fun hu => ht ?_
        have h1 : IsUnit (rootMatrix i j (-z) * (rootMatrix i j z * M t)) :=
          ((rootUnit hij (-z)).isUnit).mul hu
        rwa [← Matrix.mul_assoc, show rootMatrix i j (-z) * rootMatrix i j z = 1 by
          simpa using rootMatrix_mul_neg hij (-z), Matrix.one_mul] at h1
      rw [this]
      exact Submodule.zero_mem _
  refine FiniteFunctionSpaces.mem_of_hasDerivAt (bidegLT p q) Fam hFam _ fun z => ?_
  have hu : IsUnit ((rootUnit hij z * g : Langlands.GeneralLinear n ℂ) :
      Matrix (Fin n) (Fin n) ℂ) := Units.isUnit _
  have hd := (differentiableAt_unitsExtension hFs hu).hasFDerivAt
  have hγ : HasDerivAt (fun t : ℝ => rootMatrix i j z * M t)
      (rootMatrix i j z * ((g : Matrix (Fin n) (Fin n) ℂ) * X)) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const ((g : Matrix (Fin n) (Fin n) ℂ) * X)).const_add
      (g : Matrix (Fin n) (Fin n) ℂ)
    have h2 := h.const_mul (rootMatrix i j z)
    simpa [M] using h2
  have hcomp := hd.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp [M])
  rw [rightDerivative_eq_fderiv hFs]
  simpa [Fam, Φ, Function.comp_def, Matrix.mul_assoc] using hcomp

end Langlands.Archimedean.BlockPolynomial
