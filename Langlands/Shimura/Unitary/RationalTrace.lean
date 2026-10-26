import Langlands.Algebra.RegularTrace
import Langlands.Shimura.Unitary.RealPositivity

/-! # The source-normalized rational trace of the Harris algebra -/

noncomputable section

universe u v w

open NumberField Module Algebra
open scoped TensorProduct

namespace Langlands.Algebra

theorem regularTrace_one_tmul {R S A : Type*} [CommRing R] [CommRing S]
    [Ring A] [Algebra R S] [Algebra R A] [Module.Free R A] [Module.Finite R A]
    (a : A) :
    regularTrace S (S ⊗[R] A) ((1 : S) ⊗ₜ[R] a) =
      algebraMap R S (regularTrace R A a) := by
  have h : LinearMap.mulLeft S ((1 : S) ⊗ₜ[R] a) =
      (LinearMap.mulLeft R a).baseChange S := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s b => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  simp only [regularTrace_apply, h, LinearMap.trace_baseChange]

end Langlands.Algebra

namespace Langlands.Shimura.AlgebraInvolution

variable {F A : Type*} [Field F] [CharZero F] [Ring A] [Algebra F A]
    [FiniteDimensional F A] [IsSimpleRing A]

/-- An algebra involution preserves the regular trace on a simple algebra. -/
theorem regularTrace_apply_involution (σ : AlgebraInvolution F A) (a : A) :
    Langlands.Algebra.regularTrace F A (σ a) =
      Langlands.Algebra.regularTrace F A a := by
  let e := LinearEquiv.ofInvolutive σ.linear σ.involutive
  have h : e.conj (LinearMap.mulLeft F (σ a)) = LinearMap.mulRight F a := by
    ext b
    change σ (σ a * σ b) = b * a
    simp
  calc
    Langlands.Algebra.regularTrace F A (σ a) =
        LinearMap.trace F A (e.conj (LinearMap.mulLeft F (σ a))) :=
      (LinearMap.trace_conj' _ _).symm
    _ = LinearMap.trace F A (LinearMap.mulRight F a) := by rw [h]
    _ = Langlands.Algebra.regularTrace F A a :=
      Langlands.Algebra.trace_mulRight_eq_regularTrace F A a

end Langlands.Shimura.AlgebraInvolution

namespace Langlands.Shimura.CentralSimpleUnitaryData

variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ}

/-- The rational trace, normalized by the degree of the central simple algebra.
Its matrix-coordinate theorem below verifies the source normalization. -/
def rationalTrace (_D : CentralSimpleUnitaryData E K A n) : A →ₗ[ℚ] ℚ :=
  (n : ℚ)⁻¹ • Langlands.Algebra.regularTrace ℚ A

variable (D : CentralSimpleUnitaryData E K A n)

omit [NumberField E] [IsScalarTower E K A] [IsScalarTower ℚ E A] in
@[simp] theorem rationalTrace_apply (a : A) :
    D.rationalTrace a = (n : ℚ)⁻¹ * Langlands.Algebra.regularTrace ℚ A a := rfl

omit [NumberField E] [IsScalarTower E K A] [IsScalarTower ℚ E A] in
theorem rationalTrace_mul_comm (a b : A) :
    D.rationalTrace (a * b) = D.rationalTrace (b * a) := by
  simp only [rationalTrace_apply, Langlands.Algebra.regularTrace_mul_comm ℚ A a b]

theorem rationalTrace_involution (a : A) :
    D.rationalTrace (D.involution a) = D.rationalTrace a := by
  have : Module.Finite E A := Module.Finite.of_basis D.totallyRealBasis
  have : Module.Finite ℚ A := FiniteDimensional.trans ℚ E A
  have : IsSimpleRing A := D.simple
  exact congrArg ((n : ℚ)⁻¹ * ·)
    (D.toSecondKindInvolution.rationalInvolution.regularTrace_apply_involution a)

variable {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

/-- The regular trace in the actual real matrix splitting, before normalization. -/
theorem regularTrace_real_coordinates (a : A) :
    algebraMap ℚ ℝ (Langlands.Algebra.regularTrace ℚ A a) =
      (n : ℝ) * (2 * ∑ τ : E →+* ℝ, (Matrix.trace (C.evaluation a τ)).re) := by
  classical
  have : Module.Finite E A := Module.Finite.of_basis D.totallyRealBasis
  have : Module.Finite ℚ A := FiniteDimensional.trans ℚ E A
  calc
    algebraMap ℚ ℝ (Langlands.Algebra.regularTrace ℚ A a) =
        Langlands.Algebra.regularTrace ℝ (ℝ ⊗[ℚ] A) ((1 : ℝ) ⊗ₜ[ℚ] a) :=
      (Langlands.Algebra.regularTrace_one_tmul a).symm
    _ = LinearMap.trace ℝ ((E →+* ℝ) → Matrix (Fin n) (Fin n) ℂ)
        (LinearMap.mulLeft ℝ (C.evaluation a)) := by
      have h := trace_mulLeft_algEquiv (D.realMatrixEquiv C) ((1 : ℝ) ⊗ₜ[ℚ] a)
      simpa only [Langlands.Algebra.regularTrace_apply, realMatrixEquiv,
        C.realMatrixEquiv_one_tmul] using h.symm
    _ = ∑ τ : E →+* ℝ, 2 * n * (Matrix.trace (C.evaluation a τ)).re := by
      rw [trace_mulLeft_pi]
      simp_rw [trace_mulLeft_matrix]
    _ = (n : ℝ) * (2 * ∑ τ : E →+* ℝ, (Matrix.trace (C.evaluation a τ)).re) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro τ _
      ring

/-- The reduced trace followed by the center trace has one ordinary matrix
trace at each complex embedding; the paired real places give twice the real part. -/
theorem rationalTrace_real_coordinates (a : A) :
    algebraMap ℚ ℝ (D.rationalTrace a) =
      2 * ∑ τ : E →+* ℝ, (Matrix.trace (C.evaluation a τ)).re := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := D.rank_gt_one; omega)
  rw [rationalTrace_apply, map_mul, map_inv₀, map_natCast,
    D.regularTrace_real_coordinates C]
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- The actual matrix-coordinate normalization uniquely determines the rational
linear functional. -/
theorem rationalTrace_unique (t : A →ₗ[ℚ] ℚ)
    (ht : ∀ a, algebraMap ℚ ℝ (t a) =
      2 * ∑ τ : E →+* ℝ, (Matrix.trace (C.evaluation a τ)).re) :
    t = D.rationalTrace := by
  ext a
  apply (algebraMap ℚ ℝ).injective
  exact (ht a).trans (D.rationalTrace_real_coordinates C a).symm

end Langlands.Shimura.CentralSimpleUnitaryData
