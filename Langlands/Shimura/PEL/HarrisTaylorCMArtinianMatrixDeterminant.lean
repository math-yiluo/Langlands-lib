import Langlands.Algebra.RegularTrace
import Langlands.Shimura.PEL.HodgeDeterminant
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Rigidity of determinant polynomials of the rational algebra action -/

noncomputable section

open scoped BigOperators

set_option autoImplicit false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open Langlands.Algebra

variable {K A : Type} [Field K] [CharZero K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] [IsSimpleRing A]

private theorem traceDual_mul_repr {ι : Type} [Finite ι] [DecidableEq ι]
    (b : Module.Basis ι K A) (x : A) (i : ι) :
    b.repr x i = regularTrace K A
      (x * (regularTraceForm K A).dualBasis (regularTraceForm_nondegenerate K A) b i) := by
  let B := regularTraceForm K A
  let hB := regularTraceForm_nondegenerate K A
  let d := B.dualBasis hB b
  have h := LinearMap.BilinForm.dualBasis_repr_apply hB d x i
  rw [LinearMap.BilinForm.dualBasis_dualBasis hB (regularTraceForm_isSymm K A) b] at h
  exact h

private theorem sum_mul_traceDual {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K A) :
    (∑ i, b i * (regularTraceForm K A).dualBasis (regularTraceForm_nondegenerate K A) b i) = 1 := by
  let B := regularTraceForm K A
  let d := B.dualBasis (regularTraceForm_nondegenerate K A) b
  apply (regularTraceDual K A).injective
  apply LinearMap.ext
  intro a
  change regularTrace K A ((∑ i, b i * d i) * a) = regularTrace K A (1 * a)
  simp only [Finset.sum_mul, map_sum, one_mul]
  conv_rhs => rw [regularTrace_apply, LinearMap.trace_eq_matrix_trace K b, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, traceDual_mul_repr]
  change regularTrace K A (b i * d i * a) = regularTrace K A (a * b i * d i)
  rw [regularTrace_mul_comm K A (b i * d i) a, mul_assoc]

private theorem traceDual_intertwines {ι R : Type} [Fintype ι] [DecidableEq ι]
    [Ring R] [Algebra K R] (b : Module.Basis ι K A)
    (ρ τ : A →ₐ[K] R) (a : A) :
    let d := (regularTraceForm K A).dualBasis (regularTraceForm_nondegenerate K A) b
    ρ a * (∑ i, ρ (b i) * τ (d i)) = (∑ i, ρ (b i) * τ (d i)) * τ a := by
  dsimp only
  let d := (regularTraceForm K A).dualBasis (regularTraceForm_nondegenerate K A) b
  have hcoeff (i j : ι) : d.repr (d i * a) j = b.repr (a * b j) i := by
    rw [traceDual_mul_repr b (a * b j) i,
      show d = (regularTraceForm K A).dualBasis (regularTraceForm_nondegenerate K A) b from rfl,
      LinearMap.BilinForm.dualBasis_repr_apply]
    change regularTrace K A (d i * a * b j) = regularTrace K A (a * b j * d i)
    rw [mul_assoc, regularTrace_mul_comm K A (d i) (a * b j)]
  simp only [Finset.mul_sum, Finset.sum_mul, ← mul_assoc (ρ a), ← map_mul (f := ρ),
    mul_assoc (ρ (b _)), ← map_mul (f := τ)]
  calc
    (∑ i, ρ (a * b i) * τ (d i)) =
        ∑ i, ∑ j, b.repr (a * b i) j • (ρ (b j) * τ (d i)) := by
      apply Finset.sum_congr rfl
      intro i _
      conv_lhs => arg 1; arg 2; rw [← b.sum_repr (a * b i)]
      simp only [map_sum, map_smul, Finset.sum_mul, smul_mul_assoc]
    _ = ∑ j, ∑ i, d.repr (d j * a) i • (ρ (b j) * τ (d i)) := by
      rw [Finset.sum_comm]
      simp only [hcoeff]
    _ = ∑ j, ρ (b j) * τ (d j * a) := by
      apply Finset.sum_congr rfl
      intro j _
      conv_rhs => arg 2; arg 2; rw [← d.sum_repr (d j * a)]
      simp only [map_sum, map_smul, Finset.mul_sum, mul_smul_comm]

variable {R k J : Type} [CommRing R] [IsLocalRing R] [Field k] [Algebra K R]
  [Fintype J] [DecidableEq J]

/-- Representations with equal residue matrices are intertwined by an invertible matrix. -/
theorem exists_unit_matrix_intertwining_of_reduction
    (q : R →+* k) (hq : Function.Surjective q)
    (ρ τ : A →ₐ[K] Matrix J J R) (h : ∀ a, q.mapMatrix (ρ a) = q.mapMatrix (τ a)) :
    ∃ C : (Matrix J J R)ˣ, ∀ a, ρ a * C.val = C.val * τ a := by
  let b := Module.finBasis K A
  let d := (regularTraceForm K A).dualBasis (regularTraceForm_nondegenerate K A) b
  let M : Matrix J J R := ∑ i, ρ (b i) * τ (d i)
  have hM : q.mapMatrix M = 1 := by
    let qM : Matrix J J R →+* Matrix J J k := q.mapMatrix
    change qM M = 1
    change ∀ a, qM (ρ a) = qM (τ a) at h
    calc
      qM M = ∑ i, qM (ρ (b i * d i)) := by
        change qM (∑ i, ρ (b i) * τ (d i)) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_mul qM, ← h, ← map_mul qM, ← map_mul ρ]
      _ = 1 := by rw [← map_sum qM, ← map_sum ρ, sum_mul_traceDual, map_one, map_one]
  have hu : IsUnit M := by
    apply (Matrix.isUnit_iff_isUnit_det M).mpr
    by_contra hnon
    have hz : q M.det = 0 := by
      apply RingHom.mem_ker.mp
      rw [IsLocalRing.ker_eq_maximalIdeal q hq]
      exact (IsLocalRing.mem_maximalIdeal _).mpr hnon
    rw [RingHom.map_det, hM, Matrix.det_one] at hz
    exact one_ne_zero hz
  obtain ⟨C, hC⟩ := hu
  exact ⟨C, fun a => hC.symm ▸ traceDual_intertwines b ρ τ a⟩

/-- The universal linear combination of an actual family of square matrices. -/
def matrixPencil {S ι : Type} [CommRing S] [Fintype ι]
    (M : ι → Matrix J J S) : Matrix J J (MvPolynomial ι S) :=
  ∑ i, MvPolynomial.X (R := S) i • (MvPolynomial.C (σ := ι)).mapMatrix (M i)

theorem matrixPencil_map {S T ι : Type} [CommRing S] [CommRing T] [Fintype ι]
    (f : S →+* T) (M : ι → Matrix J J S) :
    (MvPolynomial.map f).mapMatrix (matrixPencil M) =
      matrixPencil (fun i => f.mapMatrix (M i)) := by
  apply Matrix.ext
  intro j k
  simp only [matrixPencil, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]

/-- The pencil is the matrix used by the original Lie determinant polynomial. -/
theorem hodgeDeterminant_polynomial_eq_pencil {S M ι : Type} [CommRing S] [AddCommGroup M]
    [Module S M] [Fintype ι] (b : Module.Basis J S M) (f : ι → Module.End S M) :
    Langlands.Shimura.HodgeDeterminant.polynomial b f =
      (matrixPencil (fun i => LinearMap.toMatrix b b (f i))).det := by
  unfold Langlands.Shimura.HodgeDeterminant.polynomial
  congr 1
  apply Matrix.ext
  intro j k
  simp only [Langlands.Shimura.HodgeDeterminant.matrix, matrixPencil, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Equal residue representations give the same polynomial over the local ring. -/
theorem matrixPencil_det_eq_of_reduction {ι : Type} [Fintype ι]
    (q : R →+* k) (hq : Function.Surjective q) (ρ τ : A →ₐ[K] Matrix J J R)
    (h : ∀ a, q.mapMatrix (ρ a) = q.mapMatrix (τ a)) (a : ι → A) :
    (matrixPencil (fun i => ρ (a i))).det = (matrixPencil (fun i => τ (a i))).det := by
  obtain ⟨C, hC⟩ := exists_unit_matrix_intertwining_of_reduction q hq ρ τ h
  let C' : Matrix J J (MvPolynomial ι R) := MvPolynomial.C.mapMatrix C.val
  have hu : IsUnit C' := C.isUnit.map MvPolynomial.C.mapMatrix
  have hP : matrixPencil (fun i => ρ (a i)) * C' =
      C' * matrixPencil (fun i => τ (a i)) := by
    simp only [matrixPencil, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    change MvPolynomial.C.mapMatrix (ρ (a i)) * MvPolynomial.C.mapMatrix C.val =
      MvPolynomial.C.mapMatrix C.val * MvPolynomial.C.mapMatrix (τ (a i))
    simpa only [map_mul] using congrArg MvPolynomial.C.mapMatrix (hC (a i))
  have hdet := congrArg Matrix.det hP
  simp only [Matrix.det_mul, mul_comm C'.det] at hdet
  exact (Matrix.isUnit_iff_isUnit_det C').mp hu |>.mul_right_cancel hdet

/-- Over a local ring with a specified coefficient field, the representation
determinant polynomial is the coefficient lift of its residue polynomial. -/
theorem matrixPencil_det_eq_section {ι : Type} [Fintype ι] [Algebra K k]
    (q : R →ₐ[K] k) (σ : k →ₐ[K] R) (hσ : q.comp σ = AlgHom.id K k)
    (ρ : A →ₐ[K] Matrix J J R) (a : ι → A) :
    (matrixPencil (fun i => ρ (a i))).det =
      MvPolynomial.map (σ.toRingHom.comp q.toRingHom) (matrixPencil (fun i => ρ (a i))).det := by
  let f := σ.comp q
  let τ : A →ₐ[K] Matrix J J R := f.mapMatrix.comp ρ
  have hq : Function.Surjective q := Function.RightInverse.surjective (AlgHom.congr_fun hσ)
  have hr (x : A) : q.toRingHom.mapMatrix (ρ x) = q.toRingHom.mapMatrix (τ x) := by
    ext j k
    exact (AlgHom.congr_fun hσ (q (ρ x j k))).symm
  calc
    _ = (matrixPencil (fun i => τ (a i))).det :=
      matrixPencil_det_eq_of_reduction q.toRingHom hq ρ τ hr a
    _ = _ := by
      change (matrixPencil (fun i => f.toRingHom.mapMatrix (ρ (a i)))).det =
        MvPolynomial.map f.toRingHom (matrixPencil (fun i => ρ (a i))).det
      rw [RingHom.map_det, matrixPencil_map]

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
