import Langlands.Analysis.EuclideanScalarEllipticAnalyticityTransport
import Langlands.Global.RankinSelberg.RealLocalWhittakerProperties
import Langlands.Representation.Archimedean.RealJacquetFiniteGenerationProof
import Langlands.Representation.Archimedean.RealPrincipalSeriesInfinitesimalCharacter

/-! # The elliptic matrix square sum for real Whittaker coefficients -/

noncomputable section

open Filter Set Module
open scoped ContDiff Manifold TensorProduct Matrix Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

namespace Langlands.Global.RankinSelbergGlobal.RealWhittakerElliptic

open Langlands.Analysis Langlands.Archimedean Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.RealJacquetFiniteGeneration (op op_sub opMat trace_gen_pow_mem_center
  envelopingAction_trace_gen_pow apply_skew_mem_of_rho_stable)

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

local notation "M" => Matrix (Fin n) (Fin n) ℝ
local notation "G" => Langlands.GeneralLinear n ℝ
local notation "Std" => Automorphic.realStandardKFinite n
local notation "K" => Matrix.unitaryGroup (Fin n) ℝ
local notation "R" => rightDerivative (matrixModel ℝ n)
local notation "E" => fun i j : Fin n => Matrix.single i j (1 : ℝ)

/-- The sum of squares of the right derivatives in the real matrix-unit directions. -/
def squareOperator (ds : List RealBlock) : Module.End ℂ (Std ds) :=
  ∑ i : Fin n, ∑ j : Fin n, op (realStandardLie n ds) (E i j) ^ 2

private theorem squareOperator_decomposition (ds : List RealBlock) :
    squareOperator (n := n) ds = Matrix.trace (opMat (realStandardLie n ds) ^ 2) +
      (1 / 2 : ℂ) • ∑ i : Fin n, ∑ j : Fin n, op (realStandardLie n ds) (E i j - E j i) ^ 2 := by
  let A (i j : Fin n) := op (realStandardLie n ds) (E i j)
  let T := ∑ i : Fin n, ∑ j : Fin n, A i j ^ 2
  let C := ∑ i : Fin n, ∑ j : Fin n, A i j * A j i
  have hC : Matrix.trace (opMat (realStandardLie n ds) ^ 2) = C := by
    simp only [C, pow_two, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, opMat, Matrix.of_apply, A]
  have hSkew : (∑ i : Fin n, ∑ j : Fin n, op (realStandardLie n ds) (E i j - E j i) ^ 2) =
      (2 : ℂ) • (T - C) := by
    simp only [op_sub]
    change (∑ i : Fin n, ∑ j : Fin n, (A i j - A j i) ^ 2) = _
    have hSquare (i j : Fin n) : (A i j - A j i) ^ 2 =
        A i j * A i j - A i j * A j i - A j i * A i j + A j i * A j i := by
      apply LinearMap.ext
      intro v
      simp only [pow_two, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply, map_sub]
      abel
    apply LinearMap.ext
    intro v
    simp only [hSquare, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hT : (∑ i : Fin n, ∑ j : Fin n, (A i j * A i j) v) = T v := by
      simp only [T, pow_two, LinearMap.sum_apply]
    have hCv : (∑ i : Fin n, ∑ j : Fin n, (A i j * A j i) v) = C v := by
      simp only [C, LinearMap.sum_apply]
    rw [show (∑ i : Fin n, ∑ j : Fin n, (A j i * A i j) v) = C v from Finset.sum_comm.trans hCv,
      show (∑ i : Fin n, ∑ j : Fin n, (A j i * A j i) v) = T v from Finset.sum_comm.trans hT,
      hT, hCv, two_smul]
    abel
  rw [hC, hSkew, smul_smul]
  norm_num
  change T = C + (T - C)
  abel

/-- The right-coordinate square sum preserves a finite-dimensional subspace
containing each orthogonal-finite standard vector. -/
theorem exists_invariant_squareOperator_submodule (ds : List RealBlock) (f : Std ds) :
    ∃ V : Submodule ℂ (Std ds), FiniteDimensional ℂ V ∧
      f ∈ V ∧ ∀ v ∈ V, squareOperator ds v ∈ V := by
  let ρ := realStandardRep n ds
  let π := realStandardLie n ds
  let V := Submodule.span ℂ (range fun k : K => ρ k f)
  let W := Submodule.span ℂ (range fun k : unitaryCompact ℝ n =>
    Whittaker.rightTranslation ℂ G k.val f.val)
  let : FiniteDimensional ℂ W := f.property.2
  let j : Std ds →ₗ[ℂ] (G → ℂ) := (Automorphic.realStandardKFinite n ds).subtype
  have hmap : V ≤ W.comap j := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨⟨Unitary.toUnits k, k.property⟩, rfl⟩
  let i : V →ₗ[ℂ] W := (j.comp V.subtype).codRestrict W (fun v => hmap v.property)
  have hi : Function.Injective i := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : W => w.val) h
  have hV : FiniteDimensional ℂ V := FiniteDimensional.of_injective i hi
  have hK (k : K) : ∀ v ∈ V, ρ k v ∈ V := by
    have hle : V ≤ V.comap (ρ k) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k', rfl⟩
      change ρ k (ρ k' f) ∈ V
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨k * k', rfl⟩
    exact fun _ hv => hle hv
  obtain ⟨c, hc⟩ := realStandardLie_hasInfinitesimalCharacter n ds _
    (trace_gen_pow_mem_center n 2)
  rw [envelopingAction_trace_gen_pow, Algebra.algebraMap_eq_smul_one] at hc
  have hSkew (i j : Fin n) : (E i j - E j i)ᵀ = -(E i j - E j i) := by
    simp only [Matrix.transpose_sub, Matrix.transpose_single, neg_sub]
  refine ⟨V, hV, Submodule.subset_span ⟨1, by simp [ρ]⟩, ?_⟩
  intro v hv
  rw [squareOperator_decomposition, hc, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, Module.End.one_apply]
  apply V.add_mem (V.smul_mem _ hv)
  apply V.smul_mem
  simp only [LinearMap.sum_apply, pow_two, Module.End.mul_apply]
  refine V.sum_mem fun i _ => V.sum_mem fun j _ => ?_
  have h := apply_skew_mem_of_rho_stable (isRealGKModule_realStandardModule n ds)
    V hK (E i j - E j i) (hSkew i j)
  exact h _ (h _ hv)

/-- Differentiation by right shifts on the invertible locus follows the
left-invariant field `h ↦ h X` in the matrix chart. -/
def matrixDirectionalDerivative (X : M) (f : M → ℂ) (h : M) : ℂ :=
  fderiv ℝ f h (h * X)

private theorem rightDerivative_leftTranslate (X : M) (W : G → ℂ) (g h : G) :
    R X (fun k => W (g * k)) h = R X W (g * h) := by
  unfold rightDerivative
  have he : (fun k : G => W (g * (h * k))) = fun k : G => W (g * h * k) := by
    funext k
    rw [mul_assoc]
  rw [he]
  rfl

/-- The matrix derivative of a left-translated coefficient is the original right derivative. -/
theorem matrixDirectionalDerivative_unitsExtension (X : M) {W : G → ℂ}
    (hW : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ W) (g h : G) :
    matrixDirectionalDerivative X (unitsExtension (fun k => W (g * k))) h.val = R X W (g * h) := by
  have hV : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (fun k => W (g * k)) :=
    hW.comp contMDiff_mul_left
  rw [← rightDerivative_leftTranslate X W g h, rightDerivative_eq_fderiv hV]
  rfl

private theorem matrixDirectionalDerivative_twice (X : M) {f : M → ℂ} {h : M}
    (hf : ContDiffAt ℝ ∞ f h) :
    matrixDirectionalDerivative X (matrixDirectionalDerivative X f) h =
      (fderiv ℝ (fderiv ℝ f) h (h * X)) (h * X) + fderiv ℝ f h (h * X * X) := by
  let P : M →L[ℝ] M := (ContinuousLinearMap.mul ℝ M).flip X
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) h :=
    (hf.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  change fderiv ℝ (fun y => fderiv ℝ f y (P y)) h (h * X) = _
  rw [fderiv_clm_apply hfd P.differentiableAt, P.fderiv]
  change fderiv ℝ f h (h * X * X) + (fderiv ℝ (fderiv ℝ f) h (h * X)) (h * X) = _
  exact add_comm _ _

private theorem matrixDirectionalDerivative_twice_unitsExtension (X : M) {W : G → ℂ}
    (hW : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ W)
    (hRW : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (R X W)) (g h : G) :
    matrixDirectionalDerivative X (matrixDirectionalDerivative X (unitsExtension (fun k => W (g * k)))) h.val =
      R X (R X W) (g * h) := by
  have he : matrixDirectionalDerivative X (unitsExtension (fun k => W (g * k))) =ᶠ[𝓝 h.val]
      unitsExtension (fun k => R X W (g * k)) := by
    filter_upwards [isOpen_setOf_isUnit_matrix.mem_nhds h.isUnit] with y hy
    change IsUnit y at hy
    let k : G := hy.unit
    change matrixDirectionalDerivative X (unitsExtension (fun k => W (g * k))) k.val =
      unitsExtension (fun k => R X W (g * k)) k.val
    rw [matrixDirectionalDerivative_unitsExtension X hW, unitsExtension_val]
  change fderiv ℝ (matrixDirectionalDerivative X (unitsExtension (fun k => W (g * k)))) h.val
      (h.val * X) = _
  rw [he.fderiv_eq]
  exact matrixDirectionalDerivative_unitsExtension X hRW g h

private theorem squareOperator_intertwiner {r : ℕ} {ds : List RealBlock} {a : ℝˣ}
    {B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ)}
    (hB : IsRealWhittakerIntertwiner r ds a B) (f : Automorphic.realStandardKFinite (r + 1) ds)
    (g h : Langlands.GeneralLinear (r + 1) ℝ) :
    B (squareOperator ds f) (g * h) = ∑ i : Fin (r + 1), ∑ j : Fin (r + 1),
      matrixDirectionalDerivative (Matrix.single i j 1)
        (matrixDirectionalDerivative (Matrix.single i j 1) (unitsExtension (fun k => B f (g * k)))) h.val := by
  let π := realStandardLie (r + 1) ds
  have hder (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) (v : Automorphic.realStandardKFinite (r + 1) ds) :
      B (op π X v) = rightDerivative (matrixModel ℝ (r + 1)) X (B v) :=
    hB.2.2.2.2 X v (op π X v) (realStandardLie_one_tmul_apply_coe _ _ X v)
  have hSm (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) :
      ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞
        (rightDerivative (matrixModel ℝ (r + 1)) X (B f)) := by
    rw [← hder]
    exact hB.2.1 _
  simp only [squareOperator, LinearMap.sum_apply, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change B ((op π (Matrix.single i j 1) ^ 2) f) (g * h) = _
  rw [pow_two, Module.End.mul_apply, hder, hder,
    matrixDirectionalDerivative_twice_unitsExtension _ (hB.2.1 f) (hSm _) g h]

variable (n)

local notation "J" => Fin n × Fin n
local notation "dim" => Fintype.card J
local notation "I" => Fin dim

/-- Matrix units, reindexed by their real dimension. -/
def basis : Basis I ℝ M :=
  (Matrix.stdBasis ℝ (Fin n) (Fin n)).reindex (Fintype.equivFin J)

private def fieldCoordinate (i j : I) : M →L[ℝ] ℝ :=
  ((basis n).coord j).toContinuousLinearMap.comp ((ContinuousLinearMap.mul ℝ M).flip (basis n i))

private theorem sum_fieldCoordinates (i : I) (h : M) :
    (∑ j : I, fieldCoordinate n i j h • basis n j) = h * basis n i :=
  (basis n).sum_repr (h * basis n i)

private def driftCoordinate (j : I) : M →L[ℝ] ℝ := (basis n).coord j |>.toContinuousLinearMap

private def secondCoefficient (p q : I) (h : M) : ℂ :=
  ((∑ i : I, fieldCoordinate n i p h * fieldCoordinate n i q h : ℝ) : ℂ)

/-- On matrix coordinates the square sum has the positive order-two symbol
of the translated matrix basis and drift in the direction `h`. -/
def chartOperator : CoordinateScalarOperator M dim 2 where
  basis := basis n
  coefficient k w h :=
    if hk : 1 < k.val then secondCoefficient n (w ⟨0, lt_trans zero_lt_one hk⟩) (w ⟨1, hk⟩) h
    else if hk' : 0 < k.val then (driftCoordinate n (w ⟨0, hk'⟩) h : ℂ)
    else 0

private theorem sum_words_two {A : Type*} [AddCommMonoid A] (f : I → I → A) :
    (∑ w : Fin 2 → I, f (w 0) (w 1)) = ∑ p : I, ∑ q : I, f p q := by
  calc
    _ = ∑ p : I × I, f p.1 p.2 :=
      Equiv.sum_comp (piFinTwoEquiv (fun _ : Fin 2 => I)) (fun p : I × I => f p.1 p.2)
    _ = _ := Fintype.sum_prod_type _

private theorem sum_rotate {A : Type*} [AddCommMonoid A] (f : I → I → I → A) :
    (∑ p : I, ∑ q : I, ∑ i : I, f i p q) = ∑ i : I, ∑ p : I, ∑ q : I, f i p q := by
  calc
    _ = ∑ p : I, ∑ i : I, ∑ q : I, f i p q :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

private theorem hessian_expand (i : I) (h : M) (T : M →L[ℝ] M →L[ℝ] ℂ) :
    T (h * basis n i) (h * basis n i) =
      ∑ p : I, ∑ q : I, (fieldCoordinate n i p h : ℂ) * (fieldCoordinate n i q h : ℂ) *
        T (basis n p) (basis n q) := by
  calc
    _ = T (∑ p, fieldCoordinate n i p h • basis n p) (∑ q, fieldCoordinate n i q h • basis n q) := by
      rw [sum_fieldCoordinates]
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply, smul_apply, Complex.real_smul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring

private theorem sum_hessian (f : M → ℂ) (h : M) :
    (∑ w : Fin 2 → I, secondCoefficient n (w 0) (w 1) h *
      fderiv ℝ (fderiv ℝ f) h (basis n (w 0)) (basis n (w 1))) =
      ∑ i : I, fderiv ℝ (fderiv ℝ f) h (h * basis n i) (h * basis n i) := by
  rw [sum_words_two n (fun p q => secondCoefficient n p q h *
    fderiv ℝ (fderiv ℝ f) h (basis n p) (basis n q))]
  simp only [secondCoefficient, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  rw [sum_rotate]
  exact Finset.sum_congr rfl fun i _ => (hessian_expand n i h _).symm

private theorem sum_square_basis : (∑ i : I, basis n i * basis n i) = (1 : M) := by
  rw [← (Fintype.equivFin J).sum_comp (fun i : I => basis n i * basis n i)]
  simp only [basis, Basis.reindex_apply, Equiv.symm_apply_apply, Fintype.sum_prod_type,
    Matrix.stdBasis_eq_single]
  have h (i j : Fin n) : E i j * E i j = if j = i then E i i else 0 := by
    split
    · subst j
      simpa only [one_mul] using Matrix.single_mul_single_same (1 : ℝ) i i i (1 : ℝ)
    · exact Matrix.single_mul_single_of_ne (1 : ℝ) i j i (by assumption) (1 : ℝ)
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact Matrix.sum_single_one (m := Fin n) (α := ℝ)

/-- The coordinate operator acts as the sum of the iterated matrix-field derivatives. -/
theorem chartOperator_action (f : M → ℂ) (h : M) (hf : ContDiffAt ℝ ∞ f h) :
    (chartOperator n).action f h = ∑ i : I,
      matrixDirectionalDerivative (basis n i) (matrixDirectionalDerivative (basis n i) f) h := by
  change (∑ k : Fin 3, ∑ w : Fin k.val → I, _ ) = _
  rw [Fin.sum_univ_three]
  simp only [chartOperator, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.lt_irrefl,
    Nat.not_lt_zero, Nat.one_lt_two, Nat.zero_lt_one, dite_false, dite_true, zero_mul,
    Finset.sum_const_zero, zero_add, iteratedFDeriv_two_apply, iteratedFDeriv_one_apply,
    matrixDirectionalDerivative_twice _ hf]
  rw [Finset.sum_add_distrib]
  change (∑ w : Fin 1 → I, (driftCoordinate n (w 0) h : ℂ) * fderiv ℝ f h (basis n (w 0))) +
    (∑ w : Fin 2 → I, secondCoefficient n (w 0) (w 1) h *
      fderiv ℝ (fderiv ℝ f) h (basis n (w 0)) (basis n (w 1))) = _
  rw [sum_hessian n f h]
  have hd : (∑ w : Fin 1 → I, (driftCoordinate n (w 0) h : ℂ) * fderiv ℝ f h (basis n (w 0))) =
      fderiv ℝ f h h := by
    rw [← (Equiv.funUnique (Fin 1) I).symm.sum_comp]
    simp only [Equiv.funUnique_symm_apply, ← Complex.real_smul, ← map_smul, ← map_sum]
    congr 1
    exact (basis n).sum_repr h
  rw [hd, ← map_sum]
  simp_rw [Matrix.mul_assoc]
  rw [← Matrix.mul_sum, sum_square_basis, Matrix.mul_one, add_comm]

/-- All chart coefficients are real analytic on the matrix space. -/
theorem chartOperator_analytic : (chartOperator n).AnalyticCoefficientsOn Set.univ := by
  intro k w
  by_cases hk : 1 < k.val
  · simp only [chartOperator, hk, dite_true]
    unfold secondCoefficient
    have hlin (p q : I) : AnalyticOnNhd ℝ (fun h => (fieldCoordinate n p q h : ℂ)) Set.univ :=
      (Complex.ofRealCLM.comp (fieldCoordinate n p q)).analyticOnNhd _
    simp only [Complex.ofReal_sum, Complex.ofReal_mul]
    exact Finset.analyticOnNhd_fun_sum _ fun i _ => (hlin i _).mul (hlin i _)
  · by_cases hk' : 0 < k.val
    · simp only [chartOperator, hk, hk', dite_false, dite_true]
      exact (Complex.ofRealCLM.comp (driftCoordinate n _)).analyticOnNhd _
    · simp only [chartOperator, hk, hk', dite_false]
      exact analyticOnNhd_const

/-- The symbol is positive on nonzero real covectors at invertible matrices. -/
theorem chartOperator_elliptic : (chartOperator n).IsEllipticOn {h : M | IsUnit h} := by
  intro h hh ξ hξ
  let hUnit : G := hh.unit
  let e := basis n
  change (∑ w : Fin 2 → I, secondCoefficient n (w 0) (w 1) h *
    ∏ j : Fin 2, (ξ (e (w j)) : ℂ)) ≠ 0
  simp only [Fin.prod_univ_two]
  rw [sum_words_two n (fun p q => secondCoefficient n p q h *
    ((ξ (e p) : ℂ) * (ξ (e q) : ℂ)))]
  have hscale (i : I) : (∑ p, (fieldCoordinate n i p h : ℂ) * (ξ (e p) : ℂ)) = (ξ (h * e i) : ℂ) := by
    rw [← sum_fieldCoordinates n i h]
    simp only [map_sum, map_smul, Complex.ofReal_sum, Complex.ofReal_mul, smul_eq_mul]
    rfl
  have heq : (∑ p, ∑ q, secondCoefficient n p q h * ((ξ (e p) : ℂ) * (ξ (e q) : ℂ))) =
      (↑(∑ i : I, ξ (h * e i) ^ 2) : ℂ) := by
    calc
      _ = ∑ i : I, ∑ p : I, ∑ q : I, (fieldCoordinate n i p h : ℂ) * (fieldCoordinate n i q h : ℂ) *
          ((ξ (e p) : ℂ) * (ξ (e q) : ℂ)) := by
        simp only [secondCoefficient, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
        exact sum_rotate n _
      _ = ∑ i : I, (∑ p : I, (fieldCoordinate n i p h : ℂ) * (ξ (e p) : ℂ)) ^ 2 := by
        simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => ?_
        ring
      _ = _ := by simp only [hscale, Complex.ofReal_sum, Complex.ofReal_pow]
  rw [heq]
  have hpos : 0 < ∑ i : I, ξ (h * e i) ^ 2 := by
    refine lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) fun hz => ?_
    have hz' (i : I) : ξ (h * e i) = 0 := sq_eq_zero_iff.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (ξ (h * e i)))).mp hz.symm i (Finset.mem_univ i))
    apply hξ
    ext m
    change ξ m = 0
    have hm : h * (hUnit.inv * m) = m := by
      change hUnit.val * (hUnit.inv * m) = m
      rw [← Matrix.mul_assoc, hUnit.val_inv, Matrix.one_mul]
    rw [← hm, ← e.sum_repr (hUnit.inv * m), Matrix.mul_sum, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [Matrix.mul_smul, map_smul, hz', smul_zero]
  exact_mod_cast hpos.ne'

/-- On the open matrix chart, the square operator on a standard vector
induces the elliptic differential operator on its translated coefficient. -/
theorem chartOperator_intertwiner {r : ℕ} {ds : List RealBlock} {a : ℝˣ}
    {B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ)}
    (hB : IsRealWhittakerIntertwiner r ds a B) (f : Automorphic.realStandardKFinite (r + 1) ds)
    (g h : Langlands.GeneralLinear (r + 1) ℝ) :
    (chartOperator (r + 1)).action (unitsExtension (fun k => B f (g * k))) h.val =
      B (squareOperator ds f) (g * h) := by
  have hf : ContDiffAt ℝ ∞ (unitsExtension (fun k => B f (g * k))) h.val :=
    ((contDiffOn_unitsExtension ((hB.2.1 f).comp contMDiff_mul_left)) h.val h.isUnit).contDiffAt
    (isOpen_setOf_isUnit_matrix.mem_nhds h.isUnit)
  rw [chartOperator_action _ _ _ hf, squareOperator_intertwiner hB f g h]
  rw [← (Fintype.equivFin (Fin (r + 1) × Fin (r + 1))).sum_comp]
  simp only [basis, Basis.reindex_apply, Equiv.symm_apply_apply, Fintype.sum_prod_type,
    Matrix.stdBasis_eq_single]

/-- The real square operator admits finite systems of standard vectors and
acts on all left-translated coefficients as an analytic elliptic chart operator. -/
def RealWhittakerEllipticOperatorStatement : Prop :=
  (∀ (m : ℕ) (ds : List RealBlock) (f : Automorphic.realStandardKFinite m ds),
    ∃ V : Submodule ℂ (Automorphic.realStandardKFinite m ds), FiniteDimensional ℂ V ∧
      f ∈ V ∧ ∀ v ∈ V, squareOperator ds v ∈ V) ∧
  (∀ m : ℕ, (chartOperator m).AnalyticCoefficientsOn Set.univ ∧
    (chartOperator m).IsEllipticOn {h | IsUnit h}) ∧
  ∀ (r : ℕ) (ds : List RealBlock) (a : ℝˣ)
    (B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ] (Langlands.GeneralLinear (r + 1) ℝ → ℂ)),
    IsRealWhittakerIntertwiner r ds a B → ∀ (f : Automorphic.realStandardKFinite (r + 1) ds)
      (g h : Langlands.GeneralLinear (r + 1) ℝ),
      (chartOperator (r + 1)).action (unitsExtension (fun k => B f (g * k))) h.val =
        B (squareOperator ds f) (g * h)

theorem realWhittakerEllipticOperator : RealWhittakerEllipticOperatorStatement :=
  ⟨fun _ => exists_invariant_squareOperator_submodule,
    fun m => ⟨chartOperator_analytic m, chartOperator_elliptic m⟩,
    fun _ _ _ _ => chartOperator_intertwiner⟩

end Langlands.Global.RankinSelbergGlobal.RealWhittakerElliptic
