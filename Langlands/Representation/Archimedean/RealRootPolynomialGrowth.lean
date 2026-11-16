import Langlands.Representation.Archimedean.RealLeftPolynomialCount
import Langlands.Representation.Archimedean.RealPrincipalSeriesInfinitesimalCharacter
import Mathlib.LinearAlgebra.Lagrange

/-!
# Growth on functions that are polynomial along a lower root subgroup

Let `c₀ = (a, b)` with `b < a`, `E = E_{ab}` and `e(t) = 1 + t E` (`rootUnit`). `IsRootPoly k f`
says that `t ↦ f(e(t) g)` is, for every `g`, the polynomial of degree `< k` that interpolates its
values at `t = 0, 1, …, k - 1`. `polySpace χ k` is the space of such functions in the principal
series `principalSeries ℝ n χ`.

`finrank_map_le_of_isRootPoly`: for a subspace `Y` of the `O(n)`-finite functions of a real
standard module consisting of such functions, the operators `h ↦ u h` (`h ∈ Y`, `u ∈ U_d`) span
a space of dimension at most `C (d + 1)^(n (n - 1) - 1)`.
-/

noncomputable section

open scoped Manifold ContDiff TensorProduct Matrix.Norms.Operator

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean Langlands.Algebra.UniversalEnveloping

namespace RootPolynomial

open SmoothRightAction LeftPolynomialCount RealLowerUnipotent

variable {n : ℕ} {c₀ : Fin n × Fin n}

/-! ## The root subgroup -/

/-- `E = E_{c₀}`. -/
abbrev rootMatrix (c₀ : Fin n × Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.single c₀.1 c₀.2 (1 : ℝ)

theorem rootMatrix_mul_self (hc₀ : c₀.2 < c₀.1) : rootMatrix c₀ * rootMatrix c₀ = 0 :=
  Matrix.single_mul_single_of_ne _ _ _ _ (ne_of_lt hc₀) _

theorem smul_rootMatrix_mul (hc₀ : c₀.2 < c₀.1) (s t : ℝ) :
    (s • rootMatrix c₀) * (t • rootMatrix c₀) = 0 := by
  rw [smul_mul_smul_comm, rootMatrix_mul_self hc₀, smul_zero]

private theorem one_add_mul_one_sub {R : Type*} [Ring R] (x : R) :
    (1 + x) * (1 - x) = 1 - x * x := by noncomm_ring

private theorem one_sub_mul_one_add {R : Type*} [Ring R] (x : R) :
    (1 - x) * (1 + x) = 1 - x * x := by noncomm_ring

private theorem one_add_mul_one_add {R : Type*} [Ring R] (x y : R) :
    (1 + x) * (1 + y) = 1 + (x + y) + x * y := by noncomm_ring

/-- `e(t) = 1 + t E_{c₀}`. -/
def rootUnit (hc₀ : c₀.2 < c₀.1) (t : ℝ) : Langlands.GeneralLinear n ℝ where
  val := 1 + t • rootMatrix c₀
  inv := 1 - t • rootMatrix c₀
  val_inv := by rw [one_add_mul_one_sub, smul_rootMatrix_mul hc₀, sub_zero]
  inv_val := by rw [one_sub_mul_one_add, smul_rootMatrix_mul hc₀, sub_zero]

theorem rootUnit_val (hc₀ : c₀.2 < c₀.1) (t : ℝ) :
    (rootUnit hc₀ t : Matrix (Fin n) (Fin n) ℝ) = 1 + t • rootMatrix c₀ :=
  rfl

theorem rootUnit_zero (hc₀ : c₀.2 < c₀.1) : rootUnit hc₀ 0 = 1 :=
  Units.ext (by rw [rootUnit_val, zero_smul, add_zero, Units.val_one])

theorem rootUnit_val_mul (hc₀ : c₀.2 < c₀.1) (t s : ℝ) :
    (rootUnit hc₀ t : Matrix (Fin n) (Fin n) ℝ) * (1 + s • rootMatrix c₀) =
      (rootUnit hc₀ (t + s) : Matrix (Fin n) (Fin n) ℝ) := by
  rw [rootUnit_val, rootUnit_val, one_add_mul_one_add, smul_rootMatrix_mul hc₀, add_zero,
    add_smul]

/-- `t ↦ f(e(t))` has derivative `(R(E) f)(e(t))`. -/
theorem hasDerivAt_rootUnit (hc₀ : c₀.2 < c₀.1) {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f) (t : ℝ) :
    HasDerivAt (fun s => f (rootUnit hc₀ s))
      (rightDerivative (matrixModel ℝ n) (rootMatrix c₀) f (rootUnit hc₀ t)) t := by
  set ψ := fun y : Matrix (Fin n) (Fin n) ℝ =>
    unitsExtension f ((rootUnit hc₀ t : Matrix (Fin n) (Fin n) ℝ) * y)
  have hψ : HasFDerivAt ψ (fderiv ℝ ψ 1) ((fun s : ℝ => 1 + s • rootMatrix c₀) 0) := by
    simp only [zero_smul, add_zero]
    exact (differentiableAt_unitsExtension_mul_left hf _).hasFDerivAt
  have hγ : HasDerivAt (fun s : ℝ => 1 + s • rootMatrix c₀) (rootMatrix c₀) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (rootMatrix c₀)).const_add 1
  have h0 := hψ.comp_hasDerivAt (0 : ℝ) hγ
  have hfun : ψ ∘ (fun s : ℝ => 1 + s • rootMatrix c₀) = fun s => f (rootUnit hc₀ (t + s)) := by
    funext s
    simp only [Function.comp_apply, ψ]
    rw [rootUnit_val_mul, unitsExtension_val]
  rw [hfun, ← rightDerivative_eq_fderiv_mul_left hf] at h0
  have h0' : HasDerivAt (fun s => f (rootUnit hc₀ (t + s)))
      (rightDerivative (matrixModel ℝ n) (rootMatrix c₀) f (rootUnit hc₀ t)) (t - t) := by
    rwa [sub_self]
  have h1 := h0'.comp_sub_const t t
  convert h1 using 1
  funext s
  rw [add_sub_cancel]

/-! ## Polynomials along the root subgroup -/

/-- The interpolation nodes `0, 1, …, k - 1`. -/
def node (k : ℕ) (i : Fin k) : ℂ := ((i : ℕ) : ℂ)

theorem node_injOn (k : ℕ) : Set.InjOn (node k) (Finset.univ : Finset (Fin k)) :=
  fun _ _ _ _ h => Fin.ext (Nat.cast_injective (R := ℂ) h)

/-- The Lagrange basis polynomials for the nodes `0, …, k - 1`. -/
def lag (k : ℕ) (i : Fin k) : Polynomial ℂ := Lagrange.basis Finset.univ (node k) i

/-- `t ↦ f(e(t) g)` is, for every `g`, the polynomial of degree `< k` interpolating its values
at `0, 1, …, k - 1`. -/
def IsRootPoly (hc₀ : c₀.2 < c₀.1) (k : ℕ) (f : Langlands.GeneralLinear n ℝ → ℂ) : Prop :=
  ∀ (t : ℝ) (g : Langlands.GeneralLinear n ℝ), f (rootUnit hc₀ t * g) =
    ∑ i : Fin k, (lag k i).eval (t : ℂ) * f (rootUnit hc₀ ((i : ℕ) : ℝ) * g)

/-- A function that is a polynomial of degree `< k` along every `t ↦ e(t) g` satisfies
`IsRootPoly`. -/
theorem isRootPoly_of_polynomial (hc₀ : c₀.2 < c₀.1) {k : ℕ}
    {f : Langlands.GeneralLinear n ℝ → ℂ}
    (h : ∀ g : Langlands.GeneralLinear n ℝ, ∃ q : Polynomial ℂ, q.degree < k ∧
      ∀ t : ℝ, f (rootUnit hc₀ t * g) = q.eval (t : ℂ)) : IsRootPoly hc₀ k f := by
  intro t g
  obtain ⟨q, hq, hqt⟩ := h g
  have hint := Lagrange.eq_interpolate (s := Finset.univ) (node_injOn k)
    (f := q) (by simpa using hq)
  rw [hqt t, hint, Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, mul_comm, lag, hqt]
  simp [node]

theorem isRootPoly_rightTranslation (hc₀ : c₀.2 < c₀.1) {k : ℕ}
    {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : IsRootPoly hc₀ k f) (a : Langlands.GeneralLinear n ℝ) :
    IsRootPoly hc₀ k (fun x => f (x * a)) := by
  intro t g
  simp only [mul_assoc]
  exact hf t (g * a)

theorem isRootPoly_rightDerivative (hc₀ : c₀.2 < c₀.1) {k : ℕ}
    {f : Langlands.GeneralLinear n ℝ → ℂ} (hfs : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f)
    (hf : IsRootPoly hc₀ k f) (X : Matrix (Fin n) (Fin n) ℝ) :
    IsRootPoly hc₀ k (rightDerivative (matrixModel ℝ n) X f) := by
  intro t g
  have hsm : ∀ a : Langlands.GeneralLinear n ℝ, (fun x => f (a * x)) ∈ smoothFunctions n :=
    fun a => hfs.comp contMDiff_mul_left
  have hfun : (fun x => f (rootUnit hc₀ t * x)) = ((∑ i : Fin k, (lag k i).eval (t : ℂ) •
      (⟨fun x => f (rootUnit hc₀ ((i : ℕ) : ℝ) * x), hsm _⟩ : smoothFunctions n) :
        smoothFunctions n) : Langlands.GeneralLinear n ℝ → ℂ) := by
    funext x
    rw [hf t x, Submodule.coe_sum, Finset.sum_apply]
    rfl
  rw [← rightDerivative_comp_mul_left hfs, hfun]
  have hlin := map_sum (rightDerivativeLinearMap (smoothFunctions n) (fun _ h => h) X)
    (fun i : Fin k => (lag k i).eval (t : ℂ) •
      (⟨fun x => f (rootUnit hc₀ ((i : ℕ) : ℝ) * x), hsm _⟩ : smoothFunctions n)) Finset.univ
  change rightDerivative (matrixModel ℝ n) X _ g = _
  rw [show rightDerivative (matrixModel ℝ n) X (((∑ i : Fin k, (lag k i).eval (t : ℂ) •
      (⟨fun x => f (rootUnit hc₀ ((i : ℕ) : ℝ) * x), hsm _⟩ : smoothFunctions n) :
        smoothFunctions n) : Langlands.GeneralLinear n ℝ → ℂ)) =
      rightDerivativeLinearMap (smoothFunctions n) (fun _ h => h) X _ from rfl, hlin,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]
  congr 1
  exact rightDerivative_comp_mul_left hfs _ X g

variable (χ : ℕ → ℝˣ → ℂ)

/-- The functions of the principal series that are polynomial of degree `< k` along the root
subgroup, in the sense of `IsRootPoly`. -/
def polySpace (hc₀ : c₀.2 < c₀.1) (k : ℕ) : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) where
  carrier := {f | f ∈ principalSeries ℝ n χ ∧ IsRootPoly hc₀ k f}
  zero_mem' := ⟨Submodule.zero_mem _, fun t g => by simp⟩
  add_mem' {f g} hf hg := ⟨Submodule.add_mem _ hf.1 hg.1, fun t x => by
    simp only [Pi.add_apply, hf.2 t x, hg.2 t x, mul_add, Finset.sum_add_distrib]⟩
  smul_mem' c f hf := ⟨Submodule.smul_mem _ c hf.1, fun t x => by
    simp only [Pi.smul_apply, smul_eq_mul, hf.2 t x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring⟩

theorem polySpace_smooth (hc₀ : c₀.2 < c₀.1) (k : ℕ) :
    ∀ f ∈ polySpace χ hc₀ k, ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f :=
  fun _ hf => hf.1.1

theorem rightDerivative_mem_polySpace (hc₀ : c₀.2 < c₀.1) (k : ℕ) :
    ∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ f ∈ polySpace χ hc₀ k,
      rightDerivative (matrixModel ℝ n) X f ∈ polySpace χ hc₀ k :=
  fun X _ hf => ⟨rightDerivative_mem_principalSeries χ hf.1 X,
    isRootPoly_rightDerivative hc₀ hf.1.1 hf.2 X⟩

theorem polySpace_le (hc₀ : c₀.2 < c₀.1) (k : ℕ) : polySpace χ hc₀ k ≤ smoothFunctions n :=
  fun _ hf => hf.1.1

/-- The action of `U(𝔤)` on the smooth functions preserves `polySpace`. -/
theorem envelopingAction_mem_polySpace (hc₀ : c₀.2 < c₀.1) (k : ℕ)
    (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)) (f : smoothFunctions n)
    (hf : (f : Langlands.GeneralLinear n ℝ → ℂ) ∈ polySpace χ hc₀ k) :
    (envelopingAction smoothLie u f : Langlands.GeneralLinear n ℝ → ℂ) ∈ polySpace χ hc₀ k := by
  have h := envelopingAction_inclusion_coe (polySpace_le χ hc₀ k) (fun _ hf => hf)
    (fun X _ hf => rightDerivative_mem_smoothFunctions X hf) (polySpace_smooth χ hc₀ k)
    (rightDerivative_mem_polySpace χ hc₀ k) u ⟨f, hf⟩
  have hfe : Submodule.inclusion (polySpace_le χ hc₀ k) ⟨f, hf⟩ = f := Subtype.ext rfl
  rw [hfe] at h
  rw [← h]
  exact Submodule.coe_mem _

/-! ## Evaluation at the identity -/

/-- `(R(E)^k f)(1) = 0` for `f` satisfying `IsRootPoly`. -/
theorem iterate_rightDerivative_apply_one (hc₀ : c₀.2 < c₀.1) {k : ℕ}
    {f : Langlands.GeneralLinear n ℝ → ℂ} (hfs : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f)
    (hf : IsRootPoly hc₀ k f) :
    (rightDerivative (matrixModel ℝ n) (rootMatrix c₀))^[k] f 1 = 0 := by
  set Q : Polynomial ℂ := Lagrange.interpolate Finset.univ (node k)
    (fun i : Fin k => f (rootUnit hc₀ ((i : ℕ) : ℝ))) with hQdef
  have hQ : Polynomial.derivative^[k] Q = 0 := by
    have h := Lagrange.degree_interpolate_lt (s := Finset.univ) (v := node k)
      (fun i : Fin k => f (rootUnit hc₀ ((i : ℕ) : ℝ))) (node_injOn k)
    rw [Finset.card_univ, Fintype.card_fin] at h
    by_cases hQ0 : Q = 0
    · rw [hQ0]
      exact Polynomial.iterate_derivative_zero
    · exact Polynomial.iterate_derivative_eq_zero ((Polynomial.natDegree_lt_iff_degree_lt hQ0).2 h)
  have hsm : ∀ j, ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞
      ((rightDerivative (matrixModel ℝ n) (rootMatrix c₀))^[j] f) := by
    intro j
    induction j with
    | zero => exact hfs
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact contMDiff_rightDerivative ih _
  have key : ∀ j (t : ℝ), (rightDerivative (matrixModel ℝ n) (rootMatrix c₀))^[j] f
      (rootUnit hc₀ t) = (Polynomial.derivative^[j] Q).eval (t : ℂ) := by
    intro j
    induction j with
    | zero =>
      intro t
      have h := hf t 1
      simp only [mul_one] at h
      rw [Function.iterate_zero_apply, Function.iterate_zero_apply, h, hQdef,
        Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_C, mul_comm, lag]
    | succ j ih =>
      intro t
      have h1 := hasDerivAt_rootUnit hc₀ (hsm j) t
      have hfun : (fun s => (rightDerivative (matrixModel ℝ n) (rootMatrix c₀))^[j] f
          (rootUnit hc₀ s)) = fun s : ℝ => (Polynomial.derivative^[j] Q).eval (s : ℂ) :=
        funext ih
      rw [hfun] at h1
      have h2 : HasDerivAt (fun s : ℝ => (Polynomial.derivative^[j] Q).eval (s : ℂ))
          ((Polynomial.derivative (Polynomial.derivative^[j] Q)).eval (t : ℂ)) t :=
        ((Polynomial.derivative^[j] Q).hasDerivAt (t : ℂ)).comp_ofReal
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact h1.unique h2
  have := key k 0
  rw [rootUnit_zero, hQ, Polynomial.eval_zero] at this
  exact this

/-- Upper triangular right derivatives act at `1` by scalars on the principal series. -/
theorem exists_eigen :
    ∃ μ : Fin n × Fin n → ℂ, ∀ c : Fin n × Fin n, c.1 ≤ c.2 →
      ∀ f ∈ principalSeries ℝ n χ,
        rightDerivative (matrixModel ℝ n) (Matrix.single c.1 c.2 (1 : ℝ)) f 1 = μ c * f 1 := by
  have h : ∀ c : Fin n × Fin n, ∃ m : ℂ, c.1 ≤ c.2 → ∀ f ∈ principalSeries ℝ n χ,
      rightDerivative (matrixModel ℝ n) (Matrix.single c.1 c.2 (1 : ℝ)) f 1 = m * f 1 := by
    intro c
    by_cases hc : c.1 ≤ c.2
    · let ev : principalSeries ℝ n χ →ₗ[ℂ] ℂ :=
        (LinearMap.proj (1 : Langlands.GeneralLinear n ℝ)).comp (principalSeries ℝ n χ).subtype
      let evR : principalSeries ℝ n χ →ₗ[ℂ] ℂ :=
        (LinearMap.proj (1 : Langlands.GeneralLinear n ℝ)).comp
          (rightDerivativeLinearMap (principalSeries ℝ n χ) (fun _ hf => hf.1)
            (Matrix.single c.1 c.2 (1 : ℝ)))
      have hX : (Matrix.single c.1 c.2 (1 : ℝ)).IsUpperTriangular := by
        intro i j hij
        rw [Matrix.single_apply_of_ne]
        rintro ⟨rfl, rfl⟩
        exact absurd hc (not_le.2 hij)
      obtain ⟨m, hm⟩ := ComplexPrincipalSeriesInfChar.exists_eq_smul_of_ker_le
        (φ := evR) (ψ := ev) fun f hf =>
          RealPrincipalSeriesInfChar.rightDerivative_apply_one_eq_zero f.2 hf hX
      exact ⟨m, fun _ f hf => by
        have := LinearMap.congr_fun hm ⟨f, hf⟩
        rw [LinearMap.smul_apply, smul_eq_mul] at this
        exact this⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose μ hμ using h
  exact ⟨μ, fun c hc => hμ c hc⟩

theorem envelopingAction_gen_coe (c : Fin n × Fin n) (f : smoothFunctions n) :
    (envelopingAction smoothLie (gen c) f : Langlands.GeneralLinear n ℝ → ℂ) =
      rightDerivative (matrixModel ℝ n) (Matrix.single c.1 c.2 (1 : ℝ)) f := by
  rw [gen, UniversalEnvelopingAlgebra.lift_ι_apply, stdBasis_apply, lie_one_tmul_apply_coe]

theorem envelopingAction_gen_pow_coe (j : ℕ) (f : smoothFunctions n) :
    (envelopingAction smoothLie (gen c₀ ^ j) f : Langlands.GeneralLinear n ℝ → ℂ) =
      (rightDerivative (matrixModel ℝ n) (rootMatrix c₀))^[j] f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', map_mul, Module.End.mul_apply, envelopingAction_gen_coe, ih,
      Function.iterate_succ_apply']

/-- **Evaluation at `1` kills `J`** on `polySpace`. -/
theorem eval_one_eq_zero_of_mem_J (hc₀ : c₀.2 < c₀.1) (k : ℕ) {μ : Fin n × Fin n → ℂ}
    (hμ : ∀ c : Fin n × Fin n, c.1 ≤ c.2 → ∀ f ∈ principalSeries ℝ n χ,
      rightDerivative (matrixModel ℝ n) (Matrix.single c.1 c.2 (1 : ℝ)) f 1 = μ c * f 1)
    {w : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)} (hw : w ∈ J μ c₀ k)
    (f : smoothFunctions n) (hf : (f : Langlands.GeneralLinear n ℝ → ℂ) ∈ polySpace χ hc₀ k) :
    (envelopingAction smoothLie w f : Langlands.GeneralLinear n ℝ → ℂ) 1 = 0 := by
  induction hw using Submodule.span_induction with
  | mem y hy =>
    rcases hy with ⟨c, hc, z, rfl⟩ | ⟨z, rfl⟩
    · have hF := envelopingAction_mem_polySpace χ hc₀ k z f hf
      rw [map_mul, Module.End.mul_apply, map_sub, AlgHom.commutes, LinearMap.sub_apply,
        Submodule.coe_sub, Pi.sub_apply, envelopingAction_gen_coe, hμ c hc _ hF.1,
        Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, sub_self]
    · have hF := envelopingAction_mem_polySpace χ hc₀ k z f hf
      rw [map_mul, Module.End.mul_apply, envelopingAction_gen_pow_coe]
      exact iterate_rightDerivative_apply_one hc₀ hF.1.1 hF.2
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, hx, hy, add_zero]
  | smul a x _ hx =>
    rw [map_smul, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, hx, smul_zero]

/-! ## The growth bound -/

/-- If `Ψ` vanishes only where `T` does on a finite-dimensional `P`, then `T(P)` is no bigger
than `Ψ(P)`. -/
theorem finrank_map_le_of_ker {M A B : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup A]
    [Module ℂ A] [AddCommGroup B] [Module ℂ B] (P : Submodule ℂ M) [FiniteDimensional ℂ P]
    (T : M →ₗ[ℂ] A) (Ψ : M →ₗ[ℂ] B) (h : ∀ x ∈ P, Ψ x = 0 → T x = 0) :
    Module.finrank ℂ (P.map T) ≤ Module.finrank ℂ (P.map Ψ) := by
  have hT := LinearMap.finrank_range_add_finrank_ker (T ∘ₗ P.subtype)
  have hΨ := LinearMap.finrank_range_add_finrank_ker (Ψ ∘ₗ P.subtype)
  have hker : LinearMap.ker (Ψ ∘ₗ P.subtype) ≤ LinearMap.ker (T ∘ₗ P.subtype) :=
    fun x hx => h x x.2 hx
  have := Submodule.finrank_mono hker
  rw [LinearMap.range_comp, Submodule.range_subtype] at hT hΨ
  omega

/-- **Growth on root-polynomial functions.** Let `Y` be a subspace of the `O(n)`-finite
functions of a real standard module all of whose elements satisfy `IsRootPoly hc₀ k`. Then the
operators `h ↦ u h` from `Y`, `u ∈ U_d`, span a space of dimension at most
`C (d + 1)^(n (n - 1) - 1)`. -/
theorem finrank_map_le_of_isRootPoly (ds : List RealBlock) (hc₀ : c₀.2 < c₀.1) (k : ℕ)
    (Y : Submodule ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)))
    (hY : ∀ h ∈ Y, IsRootPoly hc₀ k (h : Langlands.GeneralLinear n ℝ → ℂ)) :
    ∃ C : ℝ, ∀ d : ℕ,
      (Module.finrank ℂ ((degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) d).map
        (LinearMap.lcomp ℂ _ Y.subtype ∘ₗ
          (envelopingAction (realStandardLie n ds)).toLinearMap)) : ℝ) ≤
        C * ((d : ℝ) + 1) ^ (n * (n - 1) - 1) := by
  set χ := realPositionCharacter ds
  obtain ⟨μ, hμ⟩ := exists_eigen (n := n) χ
  set N := Fintype.card (LowIdx n)
  have hN2 := card_lowIdx_mul_two (n := n)
  have hlow := length_lowList_add_one hc₀
  refine ⟨((n + 2) ^ N * k : ℕ), fun d => ?_⟩
  -- the operators of `u` vanish on `Y` as soon as `[Ad(n̄(v)) u] = 0` for all `v`
  have hker : ∀ u ∈ degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) d,
      adMap μ c₀ k u = 0 →
        (LinearMap.lcomp ℂ _ Y.subtype ∘ₗ
          (envelopingAction (realStandardLie n ds)).toLinearMap) u = 0 := by
    intro u _ hu
    ext h : 2
    change ((envelopingAction (realStandardLie n ds) u (h : kFiniteFunctions _ _) :
      kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
        Langlands.GeneralLinear n ℝ → ℂ) = 0
    rw [realStandardLie_coe]
    have hps : (h : Langlands.GeneralLinear n ℝ → ℂ) ∈ principalSeries ℝ n χ :=
      realStandardModule_le_principalSeries n ds ((h : Y) : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)).2.1
    set h' : smoothFunctions n := ⟨h, contMDiff_of_mem_realStandardModule ((h : Y) : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)).2.1⟩
    have hF : (envelopingAction smoothLie u h' : Langlands.GeneralLinear n ℝ → ℂ) ∈
        principalSeries ℝ n χ := by
      rw [← realStandardLie_coe]
      exact realStandardModule_le_principalSeries n ds
        (envelopingAction (realStandardLie n ds) u h).2.1
    refine eq_zero_of_nbar hF fun v => ?_
    have hJ : adU (nbar v) u ∈ J μ c₀ k := by
      have := congrFun hu v
      rwa [adMap_apply, Pi.zero_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero] at this
    have hT := rightTranslate_envelopingAction (nbar v) u h'
    have h1 := congrArg (fun F : smoothFunctions n => (F : Langlands.GeneralLinear n ℝ → ℂ) 1) hT
    simp only [rightTranslate_apply, one_mul] at h1
    rw [h1]
    refine eval_one_eq_zero_of_mem_J χ hc₀ k hμ hJ _ ⟨?_, ?_⟩
    · exact rightTranslation_mem_principalSeries χ hps (nbar v)
    · exact isRootPoly_rightTranslation hc₀ (hY h h.2) (nbar v)
  have h1 := finrank_map_le_of_ker
    (A := Y →ₗ[ℂ] kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) _ _
    (adMap μ c₀ k) hker
  have h2 := finrank_map_adMap_le μ k hc₀ d
  have hN1 : 1 ≤ N := by omega
  have hexp : N + (lowList c₀).length = n * (n - 1) - 1 := by omega
  have h3 : ((1 + n) * d + 1) ^ N * (k * (d + 1) ^ (lowList c₀).length) ≤
      (n + 2) ^ N * k * (d + 1) ^ (n * (n - 1) - 1) := by
    have hb : (1 + n) * d + 1 ≤ (n + 2) * (d + 1) := by nlinarith
    calc ((1 + n) * d + 1) ^ N * (k * (d + 1) ^ (lowList c₀).length)
        ≤ ((n + 2) * (d + 1)) ^ N * (k * (d + 1) ^ (lowList c₀).length) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hb N)
      _ = (n + 2) ^ N * k * (d + 1) ^ (N + (lowList c₀).length) := by
          rw [mul_pow, pow_add]
          ring
      _ = (n + 2) ^ N * k * (d + 1) ^ (n * (n - 1) - 1) := by rw [hexp]
  have h4 := (h1.trans h2).trans h3
  have h5 : ((Module.finrank ℂ ((degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) d).map
      (LinearMap.lcomp ℂ _ Y.subtype ∘ₗ
        (envelopingAction (realStandardLie n ds)).toLinearMap)) : ℕ) : ℝ) ≤
      (((n + 2) ^ N * k * (d + 1) ^ (n * (n - 1) - 1) : ℕ) : ℝ) := by exact_mod_cast h4
  push_cast at h5 ⊢
  exact h5

end RootPolynomial

end Langlands.Archimedean
