import Langlands.Shimura.Unitary.Domain
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.AlgebraTower

/-! # Positive involutions and the twisted involution of a complex homomorphism -/

universe u v

namespace Langlands.Shimura

open scoped ComplexOrder

namespace AlgebraInvolution

variable {A : Type u} [Ring A] [Algebra ℝ A]

/-- Positivity of an involution of a real algebra: the trace of the regular
representation of `σ(x) * x` is positive for every nonzero `x`. -/
def IsPositive (σ : AlgebraInvolution ℝ A) : Prop :=
  ∀ x : A, x ≠ 0 → 0 < LinearMap.trace ℝ A (LinearMap.mulLeft ℝ (σ x * x))

namespace ComplexHom

variable {σ : AlgebraInvolution ℝ A}

/-- Precomposition with complex conjugation, again compatible with the involution. -/
noncomputable def conj (h : ComplexHom σ) : ComplexHom σ where
  hom := h.hom.comp Complex.conjAe.toAlgHom
  star_compatible z := by
    change σ (h.hom (Complex.conjAe z)) = h.hom (Complex.conjAe (star z))
    rw [h.star_compatible]
    simp [Complex.conjAe_coe]

@[simp] theorem conj_hom_apply (h : ComplexHom σ) (z : ℂ) :
    h.conj.hom z = h.hom (star z) := rfl

theorem hom_neg_I_mul_hom_I (h : ComplexHom σ) :
    h.hom (-Complex.I) * h.hom Complex.I = 1 := by
  rw [← _root_.map_mul, neg_mul, Complex.I_mul_I, neg_neg, _root_.map_one]

theorem hom_I_mul_hom_neg_I (h : ComplexHom σ) :
    h.hom Complex.I * h.hom (-Complex.I) = 1 := by
  rw [← _root_.map_mul, mul_neg, Complex.I_mul_I, neg_neg, _root_.map_one]

theorem hom_neg_one (h : ComplexHom σ) : h.hom (-1) = -1 := by
  rw [_root_.map_neg, _root_.map_one]

/-- The involution `x ↦ h(i)⁻¹ σ(x) h(i)`, written with `h(i)⁻¹ = h(-i)`. -/
noncomputable def twist (h : ComplexHom σ) : AlgebraInvolution ℝ A where
  linear :=
    { toFun x := h.hom (-Complex.I) * σ x * h.hom Complex.I
      map_add' x y := by rw [σ.apply_add, mul_add, add_mul]
      map_smul' r x := by
        rw [σ.apply_smul, mul_smul_comm, smul_mul_assoc]
        rfl }
  map_one := by
    change h.hom (-Complex.I) * σ 1 * h.hom Complex.I = 1
    rw [σ.apply_one, mul_one, h.hom_neg_I_mul_hom_I]
  map_mul x y := by
    change h.hom (-Complex.I) * σ (x * y) * h.hom Complex.I =
      (h.hom (-Complex.I) * σ y * h.hom Complex.I) *
        (h.hom (-Complex.I) * σ x * h.hom Complex.I)
    rw [σ.apply_mul]
    calc h.hom (-Complex.I) * (σ y * σ x) * h.hom Complex.I
        = h.hom (-Complex.I) * σ y * (h.hom Complex.I * h.hom (-Complex.I)) * σ x *
            h.hom Complex.I := by rw [h.hom_I_mul_hom_neg_I]; simp [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  involutive x := by
    change h.hom (-Complex.I) * σ (h.hom (-Complex.I) * σ x * h.hom Complex.I) *
      h.hom Complex.I = x
    rw [σ.apply_mul, σ.apply_mul, σ.apply_apply, h.star_compatible, h.star_compatible]
    have hI : star Complex.I = -Complex.I := by simp
    have hnI : star (-Complex.I) = Complex.I := by simp
    rw [hI, hnI]
    calc h.hom (-Complex.I) * (h.hom (-Complex.I) * (x * h.hom Complex.I)) *
          h.hom Complex.I
        = h.hom (-Complex.I * -Complex.I) * x * h.hom (Complex.I * Complex.I) := by
          simp only [_root_.map_mul, mul_assoc]
      _ = x := by
          rw [neg_mul_neg, Complex.I_mul_I, _root_.map_neg, _root_.map_one, neg_mul,
            one_mul, mul_neg, mul_one, neg_neg]

@[simp] theorem twist_apply (h : ComplexHom σ) (x : A) :
    h.twist x = h.hom (-Complex.I) * σ x * h.hom Complex.I := rfl

/-- Conjugating the homomorphism does not change its twisted involution. -/
theorem twist_conj (h : ComplexHom σ) (x : A) : h.conj.twist x = h.twist x := by
  have h2 : star Complex.I = -Complex.I := by simp
  simp only [twist_apply, conj_hom_apply, h2, _root_.map_neg, neg_mul, mul_neg, neg_neg]

end ComplexHom

end AlgebraInvolution

section RegularTrace

/-- Coordinates of a matrix in the entrywise basis built from a basis of the entries. -/
theorem matrix_repr_apply {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (b : Module.Basis ι R M) (n : ℕ) (x : Matrix (Fin n) (Fin n) M) (p q : Fin n) (k : ι) :
    (b.matrix (Fin n) (Fin n)).repr x (p, q, k) = b.repr (x p q) k := by
  simp [Module.Basis.matrix, Pi.basis_repr]

/-- The real trace of left multiplication on complex `n × n` matrices. -/
theorem trace_mulLeft_matrix (n : ℕ) (y : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.trace ℝ (Matrix (Fin n) (Fin n) ℂ) (LinearMap.mulLeft ℝ y) =
      2 * n * (Matrix.trace y).re := by
  classical
  let b := Complex.basisOneI.matrix (Fin n) (Fin n)
  rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, b, Module.Basis.matrix_apply,
    LinearMap.mulLeft_apply, matrix_repr_apply, Matrix.mul_single_apply_same,
    Fintype.sum_prod_type, Fin.sum_univ_two, Complex.coe_basisOneI,
    Complex.coe_basisOneI_repr]
  simp [Matrix.trace, Finset.sum_add_distrib, Finset.mul_sum, Complex.re_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The real trace of left multiplication on a finite product of real algebras. -/
theorem trace_mulLeft_pi {I : Type v} [Fintype I] [DecidableEq I] {B : I → Type u}
    [∀ i, Ring (B i)] [∀ i, Algebra ℝ (B i)] [∀ i, Module.Free ℝ (B i)]
    [∀ i, Module.Finite ℝ (B i)] (y : ∀ i, B i) :
    LinearMap.trace ℝ (∀ i, B i) (LinearMap.mulLeft ℝ y) =
      ∑ i, LinearMap.trace ℝ (B i) (LinearMap.mulLeft ℝ (y i)) := by
  classical
  let b := fun i => Module.Free.chooseBasis ℝ (B i)
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basis b), Matrix.trace]
  simp_rw [fun i => LinearMap.trace_eq_matrix_trace ℝ (b i), Matrix.trace]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.diag, LinearMap.toMatrix_apply, Pi.basis_apply, Pi.basis_repr]

end RegularTrace

open AlgebraInvolution

/-- Conjugate transpose on complex matrices is a positive involution. -/
theorem trace_mulLeft_conjTranspose_mul_self_pos {n : ℕ}
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ≠ 0) :
    0 < LinearMap.trace ℝ (Matrix (Fin n) (Fin n) ℂ)
      (LinearMap.mulLeft ℝ (star x * x)) := by
  rw [trace_mulLeft_matrix]
  have h0 : 0 ≤ (Matrix.conjTranspose x * x).trace :=
    Matrix.PosSemidef.trace_nonneg (Matrix.posSemidef_conjTranspose_mul_self x)
  have h1 : (Matrix.conjTranspose x * x).trace ≠ 0 := fun h =>
    hx (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h)
  have hpos : 0 < ((Matrix.conjTranspose x * x).trace).re :=
    (Complex.lt_def.mp (lt_of_le_of_ne h0 h1.symm)).1
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Matrix.trace] at hpos
    · exact hn
  change 0 < 2 * (n : ℝ) * ((Matrix.conjTranspose x * x).trace).re
  positivity

/-- The conjugate-transpose involution on each archimedean factor. -/
noncomputable def piConjTranspose (n : ℕ) (I : Type v) :
    AlgebraInvolution ℝ (I → Matrix (Fin n) (Fin n) ℂ) :=
  AlgebraInvolution.pi fun _ => AlgebraInvolution.ofStar

@[simp] theorem piConjTranspose_apply (n : ℕ) (I : Type v)
    (x : I → Matrix (Fin n) (Fin n) ℂ) : piConjTranspose n I x = star x := rfl

theorem piConjTranspose_isPositive (n : ℕ) (I : Type v) [Fintype I] [DecidableEq I] :
    (piConjTranspose n I).IsPositive := by
  intro x hx
  rw [piConjTranspose_apply, trace_mulLeft_pi]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · by_cases hj : x j = 0
    · simp [Pi.mul_apply, Pi.star_apply, hj]
    · exact (trace_mulLeft_conjTranspose_mul_self_pos hj).le
  · exact trace_mulLeft_conjTranspose_mul_self_pos hi

theorem correctedComplexHom_twist (n r : ℕ) (x : Matrix (Fin n) (Fin n) ℂ) :
    correctedComplexHom n r (-Complex.I) * signatureAdjoint n r x *
      correctedComplexHom n r Complex.I = star x := by
  have hl : correctedComplexHom n r (-Complex.I) * signatureMatrix n r =
      Matrix.scalar (Fin n) Complex.I := by
    rw [correctedComplexHom_apply, signatureMatrix, Matrix.diagonal_mul_diagonal,
      Matrix.scalar_apply]
    apply congrArg Matrix.diagonal
    funext i
    split_ifs <;> simp
  have hr : signatureMatrix n r * correctedComplexHom n r Complex.I =
      Matrix.scalar (Fin n) (-Complex.I) := by
    rw [correctedComplexHom_apply, signatureMatrix, Matrix.diagonal_mul_diagonal,
      Matrix.scalar_apply]
    apply congrArg Matrix.diagonal
    funext i
    split_ifs <;> simp
  change correctedComplexHom n r (-Complex.I) *
      (signatureMatrix n r * star x * signatureMatrix n r) *
      correctedComplexHom n r Complex.I = star x
  calc correctedComplexHom n r (-Complex.I) *
        (signatureMatrix n r * star x * signatureMatrix n r) *
        correctedComplexHom n r Complex.I
      = (correctedComplexHom n r (-Complex.I) * signatureMatrix n r) * star x *
          (signatureMatrix n r * correctedComplexHom n r Complex.I) := by
        simp only [mul_assoc]
    _ = star x := by
        rw [hl, hr, Matrix.scalar_commute _ (fun _ => Commute.all _ _), mul_assoc,
          ← _root_.map_mul, mul_neg, Complex.I_mul_I, neg_neg, _root_.map_one, mul_one]

/-- The twisted involution of the corrected Harris homomorphism is conjugate
transposition on every archimedean factor. -/
theorem harrisArchimedeanHom_twist (n : ℕ) (I : Type v) [DecidableEq I]
    (distinguished : I) (x : I → Matrix (Fin n) (Fin n) ℂ) :
    (harrisArchimedeanHom n I distinguished).twist x = star x := by
  funext i
  exact correctedComplexHom_twist n _ (x i)

/-- Kottwitz's homomorphism `h₀` for Harris's corrected datum: the corrected
homomorphism precomposed with complex conjugation. -/
noncomputable def kottwitzHom (n : ℕ) (I : Type v) [DecidableEq I] (distinguished : I) :
    ComplexHom (harrisArchimedeanInvolution n I distinguished) :=
  (harrisArchimedeanHom n I distinguished).conj

/-- The positivity certificate for Harris's standard archimedean model. -/
theorem kottwitzHom_twist_isPositive (n : ℕ) (I : Type v) [Fintype I] [DecidableEq I]
    (distinguished : I) : (kottwitzHom n I distinguished).twist.IsPositive := by
  intro x hx
  have hfun : ∀ y, (kottwitzHom n I distinguished).twist y = piConjTranspose n I y :=
    fun y => by
      rw [kottwitzHom, ComplexHom.twist_conj, harrisArchimedeanHom_twist,
        piConjTranspose_apply]
  rw [hfun]
  exact piConjTranspose_isPositive n I x hx

end Langlands.Shimura
