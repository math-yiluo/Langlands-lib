import Mathlib

/-! # Finite-family norms of ordered derivative tensors -/

noncomputable section
open scoped BigOperators ContDiff
open Function
set_option autoImplicit false

namespace Langlands.Analysis

universe uA uI uJ uE uF

variable {A : Type uA} [Fintype A]
  {I : Type uI} [Fintype I] {J : Type uJ} [Fintype J]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type uF} [NormedAddCommGroup F]

/-- The Euclidean norm of a finite family of vectors in a normed space. -/
def finiteFamilyL2Norm (f : I → F) : ℝ :=
  ‖WithLp.toLp 2 f‖

theorem finiteFamilyL2Norm_eq_sqrt (f : I → F) :
    finiteFamilyL2Norm f = Real.sqrt (∑ i, ‖f i‖ ^ 2) := by
  exact PiLp.norm_eq_of_L2 _

theorem finiteFamilyL2Norm_nonneg (f : I → F) :
    0 ≤ finiteFamilyL2Norm f :=
  norm_nonneg _

theorem finiteFamilyL2Norm_add_le (f g : I → F) :
    finiteFamilyL2Norm (fun i => f i + g i) ≤
      finiteFamilyL2Norm f + finiteFamilyL2Norm g := by
  exact norm_add_le (WithLp.toLp 2 f) (WithLp.toLp 2 g)

theorem finiteFamilyL2Norm_congr {f g : I → F} (h : ∀ i, f i = g i) :
    finiteFamilyL2Norm f = finiteFamilyL2Norm g := by
  congr 1
  exact funext h

theorem finiteFamilyL2Norm_reindex (e : I ≃ J) (f : J → F) :
    finiteFamilyL2Norm (f ∘ e) = finiteFamilyL2Norm f := by
  simp only [finiteFamilyL2Norm_eq_sqrt, comp_apply]
  exact congrArg Real.sqrt (e.sum_comp (fun j => ‖f j‖ ^ 2))

variable [NormedSpace ℝ F]

/-- The norm of every ordered derivative word, jointly over a finite family.
The directions need not be a basis or have norm one. -/
def orderedDerivativeFamilyNorm (v : A → E) (p : ℕ) (f : I → E → F) (x : E) : ℝ :=
  finiteFamilyL2Norm (fun iw : I × (Fin p → A) =>
    iteratedFDeriv ℝ p (f iw.1) x (v ∘ iw.2))

theorem orderedDerivativeFamilyNorm_eq_sqrt
    (v : A → E) (p : ℕ) (f : I → E → F) (x : E) :
    orderedDerivativeFamilyNorm v p f x =
      Real.sqrt (∑ i, ∑ w : Fin p → A,
        ‖iteratedFDeriv ℝ p (f i) x (v ∘ w)‖ ^ 2) := by
  rw [orderedDerivativeFamilyNorm, finiteFamilyL2Norm_eq_sqrt, Fintype.sum_prod_type]

theorem orderedDerivativeFamilyNorm_nonneg
    (v : A → E) (p : ℕ) (f : I → E → F) (x : E) :
    0 ≤ orderedDerivativeFamilyNorm v p f x :=
  finiteFamilyL2Norm_nonneg _

theorem orderedDerivativeFamilyNorm_zero
    (v : A → E) (f : I → E → F) (x : E) :
    orderedDerivativeFamilyNorm v 0 f x = finiteFamilyL2Norm (fun i => f i x) := by
  simp [orderedDerivativeFamilyNorm_eq_sqrt, finiteFamilyL2Norm_eq_sqrt]

theorem orderedDerivativeFamilyNorm_reindex (e : I ≃ J)
    (v : A → E) (p : ℕ) (f : J → E → F) (x : E) :
    orderedDerivativeFamilyNorm v p (fun i => f (e i)) x =
      orderedDerivativeFamilyNorm v p f x := by
  simp only [orderedDerivativeFamilyNorm_eq_sqrt]
  exact congrArg Real.sqrt (e.sum_comp
    (fun i => ∑ w : Fin p → A, ‖iteratedFDeriv ℝ p (f i) x (v ∘ w)‖ ^ 2))

/-- For a one-element family the norm is the complete ordered tensor norm of its
single function. -/
theorem orderedDerivativeFamilyNorm_unique [Unique I]
    (v : A → E) (p : ℕ) (f : I → E → F) (x : E) :
    orderedDerivativeFamilyNorm v p f x =
      Real.sqrt (∑ w : Fin p → A,
        ‖iteratedFDeriv ℝ p (f default) x (v ∘ w)‖ ^ 2) := by
  rw [orderedDerivativeFamilyNorm_eq_sqrt, Fintype.sum_unique]

/-- With the standard basis of `EuclideanSpace ℝ (Fin d)`, a singleton scalar
family gives the ordered top-derivative tensor norm used in
`ConstantCoefficientEllipticL2EstimateStatement`. -/
theorem orderedDerivativeFamilyNorm_euclidean_singleton (d r : ℕ)
    (G : EuclideanSpace ℝ (Fin d) → ℂ) (x : EuclideanSpace ℝ (Fin d)) :
    orderedDerivativeFamilyNorm ⇑(EuclideanSpace.basisFun (Fin d) ℝ) r
        (fun _ : Unit => G) x =
      Real.sqrt (∑ w : Fin r → Fin d,
        ‖iteratedFDeriv ℝ r G x
          (fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j))‖ ^ 2) :=
  orderedDerivativeFamilyNorm_unique _ _ _ _

theorem orderedDerivativeFamilyNorm_add_le
    (v : A → E) (p : ℕ) (f g : I → E → F) (x : E)
    (hf : ∀ i, ContDiffAt ℝ p (f i) x) (hg : ∀ i, ContDiffAt ℝ p (g i) x) :
    orderedDerivativeFamilyNorm v p (fun i y => f i y + g i y) x ≤
      orderedDerivativeFamilyNorm v p f x + orderedDerivativeFamilyNorm v p g x := by
  unfold orderedDerivativeFamilyNorm
  convert finiteFamilyL2Norm_add_le
    (fun iw : I × (Fin p → A) => iteratedFDeriv ℝ p (f iw.1) x (v ∘ iw.2))
    (fun iw : I × (Fin p → A) => iteratedFDeriv ℝ p (g iw.1) x (v ∘ iw.2)) using 1
  congr 1
  funext iw
  rw [fun_iteratedFDeriv_add_apply (hf iw.1) (hg iw.1)]
  rfl

/-- Evaluation at a fixed direction commutes with an iterated derivative. -/
theorem iteratedFDeriv_fixed_lineDeriv
    (p : ℕ) {f : E → F} {x : E} (hf : ContDiffAt ℝ (p + 1) f x)
    (m : Fin p → E) (a : E) :
    iteratedFDeriv ℝ p (fun y => fderiv ℝ f y a) x m =
      iteratedFDeriv ℝ (p + 1) f x (Fin.snoc m a) := by
  let ev : (E →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F a
  have hfd : ContDiffAt ℝ p (fderiv ℝ f) x :=
    hf.fderiv_right (by simp)
  have h := ev.iteratedFDeriv_comp_left hfd (le_refl _)
  have he := congrArg (fun T => T m) h
  rw [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  exact he

/-- The first-direction index and the remaining word recover every word of
length `p + 1` exactly once. -/
theorem orderedDerivativeFamilyNorm_lineDeriv
    (v : A → E) (p : ℕ) (f : I → E → F) (x : E)
    (hf : ∀ i, ContDiffAt ℝ (p + 1) (f i) x) :
    orderedDerivativeFamilyNorm v p
        (fun ai : A × I => fun y => fderiv ℝ (f ai.2) y (v ai.1)) x =
      orderedDerivativeFamilyNorm v (p + 1) f x := by
  simp only [orderedDerivativeFamilyNorm_eq_sqrt, Fintype.sum_prod_type]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [iteratedFDeriv_fixed_lineDeriv p (hf i)]
  have h := (Fin.snocEquiv (fun _ : Fin (p + 1) => A)).sum_comp
    (fun w => ‖iteratedFDeriv ℝ (p + 1) (f i) x (v ∘ w)‖ ^ 2)
  change (∑ aw : A × (Fin p → A),
    ‖iteratedFDeriv ℝ (p + 1) (f i) x (v ∘ Fin.snoc aw.2 aw.1)‖ ^ 2) = _ at h
  simpa only [Fintype.sum_prod_type, ← Fin.comp_snoc] using h

end Langlands.Analysis
