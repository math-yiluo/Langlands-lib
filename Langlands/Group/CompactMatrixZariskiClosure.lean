import Langlands.GroupScheme.GeneralLinear
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.MeasureTheory.Group.Integral

/-! # Compact real matrix groups are cut out by polynomials (Chevalley) -/

noncomputable section

open MvPolynomial MeasureTheory
open Langlands.GroupScheme.GeneralLinear

namespace Langlands.Group.CompactMatrixZariski

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The variables of the right translate `x ↦ x * c`, with the entries of `c` and `c⁻¹` kept as
coefficient variables. -/
def rightTranslationVar :
    Coordinate n → MvPolynomial (Coordinate n) (MvPolynomial (Coordinate n) ℝ)
  | .entry i j => ∑ k, X (.entry i k) * C (X (.entry k j))
  | .inverseEntry i j => ∑ k, C (X (.inverseEntry i k)) * X (.inverseEntry k j)

/-- The right translate of `q`, with polynomial coefficients in the translating matrix. -/
def rightTranslation (q : MvPolynomial (Coordinate n) ℝ) :
    MvPolynomial (Coordinate n) (MvPolynomial (Coordinate n) ℝ) :=
  aeval rightTranslationVar q

theorem eval₂_rightTranslationVar (x c : GL n ℝ) (κ : Coordinate n) :
    eval₂ (eval (values c)) (values x) (rightTranslationVar κ) = values (x * c) κ := by
  cases κ with
  | entry i j =>
    simp [rightTranslationVar, values, Matrix.mul_apply, eval₂_sum]
  | inverseEntry i j =>
    simp [rightTranslationVar, values, Matrix.mul_apply, eval₂_sum, mul_inv_rev]

theorem eval₂_rightTranslation (q : MvPolynomial (Coordinate n) ℝ) (x c : GL n ℝ) :
    eval₂ (eval (values c)) (values x) (rightTranslation q) = eval (values (x * c)) q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [rightTranslation]
  | add p q hp hq => simp only [rightTranslation, map_add, eval₂_add] at *; rw [hp, hq]
  | mul_X p κ hp =>
    simp only [rightTranslation, map_mul, aeval_X, eval₂_mul] at *
    rw [hp, eval₂_rightTranslationVar, eval_X]

section Average

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
  [OpensMeasurableSpace K] (μ : Measure K) [IsFiniteMeasure μ]
  (φ : K → GL n ℝ)

/-- The average of the right translates `x ↦ q (x * φ k)` against `μ`, as a polynomial. -/
def average (q : MvPolynomial (Coordinate n) ℝ) : MvPolynomial (Coordinate n) ℝ :=
  ∑ d ∈ (rightTranslation q).support,
    monomial d (∫ k, eval (values (φ k)) ((rightTranslation q).coeff d) ∂μ)

theorem continuous_values : Continuous (values : GL n ℝ → Coordinate n → ℝ) := by
  refine continuous_pi fun κ => ?_
  cases κ with
  | entry i j =>
    exact Units.continuous_val.matrix_elem i j
  | inverseEntry i j =>
    exact Units.continuous_coe_inv.matrix_elem i j

theorem eval_average (hφ : Continuous φ) (q : MvPolynomial (Coordinate n) ℝ) (x : GL n ℝ) :
    eval (values x) (average μ φ q) = ∫ k, eval (values (x * φ k)) q ∂μ := by
  simp_rw [← eval₂_rightTranslation q x, eval₂_eq]
  have hint : ∀ d ∈ (rightTranslation q).support, Integrable
      (fun k => eval (values (φ k)) ((rightTranslation q).coeff d) *
        ∏ i ∈ d.support, values x i ^ d i) μ := by
    intro d _
    refine Continuous.integrable_of_hasCompactSupport ?_
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
    exact ((MvPolynomial.continuous_eval _).comp (continuous_values.comp hφ)).mul continuous_const
  rw [integral_finsetSum _ hint]
  simp only [average, map_sum, eval_monomial, integral_mul_const, Finsupp.prod]

end Average

section Approximation

omit [Fintype n] [DecidableEq n] in
/-- The coordinate type is finite. -/
theorem finite_coordinate [Finite n] : Finite (Coordinate n) := by
  have e : Coordinate n ≃ (n × n) ⊕ (n × n) :=
    { toFun := fun
        | .entry i j => Sum.inl (i, j)
        | .inverseEntry i j => Sum.inr (i, j)
      invFun := fun
        | Sum.inl (i, j) => .entry i j
        | Sum.inr (i, j) => .inverseEntry i j
      left_inv := fun κ => by cases κ <;> rfl
      right_inv := fun s => by rcases s with ⟨i, j⟩ | ⟨i, j⟩ <;> rfl }
  exact Finite.of_equiv _ e.symm

/-- The coordinate projections as continuous functions. -/
def coordinateFunction (κ : Coordinate n) : C(Coordinate n → ℝ, ℝ) :=
  ⟨fun v => v κ, continuous_apply κ⟩

omit [Fintype n] [DecidableEq n] in
theorem aeval_coordinateFunction_apply (q : MvPolynomial (Coordinate n) ℝ)
    (v : Coordinate n → ℝ) : (aeval coordinateFunction q : C(Coordinate n → ℝ, ℝ)) v =
      eval v q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [_root_.algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p κ hp => simp [hp, coordinateFunction]

theorem values_injective : Function.Injective (values : GL n ℝ → Coordinate n → ℝ) := by
  intro g h hgh
  ext i j
  exact congrFun hgh (.entry i j)

/-- Polynomial approximation of the indicator of one of two disjoint compact sets of
invertible matrices. -/
theorem exists_polynomial_near_zero_one {A₀ A₁ : Set (GL n ℝ)} (h₀ : IsCompact A₀)
    (h₁ : IsCompact A₁) (hd : Disjoint A₀ A₁) :
    ∃ q : MvPolynomial (Coordinate n) ℝ,
      (∀ x ∈ A₀, |eval (values x) q| < 1 / 4) ∧
        (∀ x ∈ A₁, |eval (values x) q - 1| < 1 / 4) := by
  have : Finite (Coordinate n) := finite_coordinate
  have := Fintype.ofFinite (Coordinate n)
  have hB₀ := h₀.image (continuous_values (n := n))
  have hB₁ := h₁.image (continuous_values (n := n))
  have hdB : Disjoint (values '' A₀) (values '' A₁) :=
    (Set.disjoint_image_iff values_injective).mpr hd
  obtain ⟨f, hf₀, hf₁, -⟩ :=
    exists_continuous_zero_one_of_isClosed hB₀.isClosed hB₁.isClosed hdB
  let A : Subalgebra ℝ C(Coordinate n → ℝ, ℝ) := (aeval coordinateFunction).range
  have hA : A.SeparatesPoints := by
    intro v w hvw
    obtain ⟨κ, hκ⟩ := Function.ne_iff.mp hvw
    exact ⟨_, ⟨coordinateFunction κ, ⟨X κ, by simp⟩, rfl⟩, hκ⟩
  obtain ⟨g, ⟨q, rfl⟩, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints hA f
      (hB₀.union hB₁) (ε := 1 / 4) (by norm_num)
  refine ⟨q, fun x hx => ?_, fun x hx => ?_⟩
  · have h := hg (values x) (Or.inl ⟨x, hx, rfl⟩)
    rw [hf₀ ⟨x, hx, rfl⟩] at h
    simpa [aeval_coordinateFunction_apply, Real.norm_eq_abs] using h
  · have h := hg (values x) (Or.inr ⟨x, hx, rfl⟩)
    rw [hf₁ ⟨x, hx, rfl⟩] at h
    simpa [aeval_coordinateFunction_apply, Real.norm_eq_abs] using h

end Approximation

section Chevalley

/-- **Chevalley.** A compact subgroup of `GL n ℝ` is cut out by polynomials in the matrix
entries and inverse entries: every invertible matrix outside it is separated from it by such a
polynomial. -/
theorem exists_polynomial_separating (C : Subgroup (GL n ℝ))
    (hC : IsCompact (C : Set (GL n ℝ))) {g : GL n ℝ} (hg : g ∉ C) :
    ∃ p : MvPolynomial (Coordinate n) ℝ,
      (∀ c ∈ C, eval (values c) p = 0) ∧ eval (values g) p ≠ 0 := by
  have hd : Disjoint (C : Set (GL n ℝ)) ((g * ·) '' C) := by
    rw [Set.disjoint_left]
    rintro _ hx ⟨c, hc, rfl⟩
    exact hg (by simpa using C.mul_mem hx (C.inv_mem hc))
  obtain ⟨q, hq₀, hq₁⟩ :=
    exists_polynomial_near_zero_one hC (hC.image (continuous_const.mul continuous_id)) hd
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let : MeasurableSpace C := borel C
  have : BorelSpace C := ⟨rfl⟩
  let K₀ : TopologicalSpace.PositiveCompacts C := ⊤
  let μ : Measure C := Measure.haarMeasure K₀
  have hμ : μ Set.univ = 1 := by simpa [K₀] using Measure.haarMeasure_self (K₀ := K₀)
  have : IsFiniteMeasure μ := ⟨by rw [hμ]; exact ENNReal.one_lt_top⟩
  let φ : C → GL n ℝ := Subtype.val
  have hφ : Continuous φ := continuous_subtype_val
  have hint : ∀ ψ : C → GL n ℝ, Continuous ψ →
      Integrable (fun k => eval (values (ψ k)) q) μ := fun ψ hψ =>
    Continuous.integrable_of_hasCompactSupport
      ((MvPolynomial.continuous_eval _).comp (continuous_values.comp hψ))
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  refine ⟨average μ φ q - MvPolynomial.C (∫ k, eval (values (φ k)) q ∂μ),
    fun c hc => ?_, ?_⟩
  · rw [map_sub, eval_C, eval_average μ φ hφ, sub_eq_zero]
    exact integral_mul_left_eq_self (fun k : C => eval (values (φ k)) q) ⟨c, hc⟩
  · have h1 := hint (fun k => g * φ k) (continuous_const.mul hφ)
    have h0 := hint φ hφ
    rw [map_sub, eval_C, eval_average μ φ hφ, ← integral_sub h1 h0]
    have hlow : ∫ _k : C, (1 / 2 : ℝ) ∂μ ≤
        ∫ k, (eval (values (g * φ k)) q - eval (values (φ k)) q) ∂μ := by
      refine integral_mono (integrable_const _) (h1.sub h0) fun k => ?_
      have a := hq₀ (φ k) k.2
      have b := hq₁ (g * φ k) ⟨φ k, k.2, rfl⟩
      rw [abs_lt] at a b
      dsimp only
      linarith [a.1, a.2, b.1, b.2]
    have hpos : 0 < ∫ _k : C, (1 / 2 : ℝ) ∂μ := by
      simp [integral_const, measureReal_def, hμ]
    exact (lt_of_lt_of_le hpos hlow).ne'

end Chevalley

section LeftTranslation

variable {k : Type*} [Field k]

/-- The variables of the left translate `x ↦ a * x` by a fixed invertible matrix. -/
def leftTranslationVar (a : GL n k) : Coordinate n → MvPolynomial (Coordinate n) k
  | .entry i j => ∑ l, C ((a : Matrix n n k) i l) * X (.entry l j)
  | .inverseEntry i j => ∑ l, X (.inverseEntry i l) * C ((a⁻¹ : GL n k) l j)

/-- The left translate of a polynomial in matrix and inverse entries. -/
def leftTranslate (a : GL n k) (p : MvPolynomial (Coordinate n) k) :
    MvPolynomial (Coordinate n) k :=
  bind₁ (leftTranslationVar a) p

theorem eval_leftTranslate (a x : GL n k) (p : MvPolynomial (Coordinate n) k) :
    eval (values x) (leftTranslate a p) = eval (values (a * x)) p := by
  change aeval (values x) (bind₁ (leftTranslationVar a) p) = aeval (values (a * x)) p
  rw [aeval_bind₁]
  refine congrArg (fun f => aeval f p) (funext fun κ => ?_)
  cases κ with
  | entry i j => simp [leftTranslationVar, values, Matrix.mul_apply]
  | inverseEntry i j => simp [leftTranslationVar, values, Matrix.mul_apply, mul_inv_rev]

end LeftTranslation

end Langlands.Group.CompactMatrixZariski
