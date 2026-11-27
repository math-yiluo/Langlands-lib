import Langlands.Algebra.RegularTrace

/-! # Averaging to an intertwiner using the regular trace -/

noncomputable section

open scoped BigOperators

set_option autoImplicit false

namespace Langlands.Algebra

variable {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] [IsSimpleRing A]
  {I : Type*} [Fintype I] [DecidableEq I] (b : Module.Basis I K A)

local notation "d" =>
  LinearMap.BilinForm.dualBasis (regularTraceForm K A) (regularTraceForm_nondegenerate K A) b

private theorem repr_eq_trace (x : A) (i : I) :
    b.repr x i = regularTrace K A (x * d i) := by
  have h := LinearMap.BilinForm.dualBasis_repr_apply (regularTraceForm_nondegenerate K A) d x i
  rw [LinearMap.BilinForm.dualBasis_dualBasis _ (regularTraceForm_isSymm K A) b] at h
  exact h

private theorem sum_basis_mul_dual : (∑ i, b i * d i) = 1 := by
  apply (regularTraceDual K A).injective
  apply LinearMap.ext
  intro a
  change regularTrace K A ((∑ i, b i * d i) * a) = regularTrace K A (1 * a)
  simp only [Finset.sum_mul, map_sum, one_mul]
  conv_rhs => rw [regularTrace_apply, LinearMap.trace_eq_matrix_trace K b, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, repr_eq_trace b]
  change regularTrace K A (b i * d i * a) = regularTrace K A (a * b i * d i)
  rw [regularTrace_mul_comm K A (b i * d i) a, mul_assoc]

variable {R S : Type*} [Ring R] [Algebra K R] [Ring S] [Algebra K S]
  (ρ τ : A →ₐ[K] R)

/-- Apply the two representations to a regular-trace dual basis pair on
either side of the supplied element. -/
def regularTraceAverage (x : R) : R :=
  ∑ i, ρ (b i) * x * τ (d i)

/-- Averaging over dual bases produces an intertwiner. -/
theorem regularTraceAverage_intertwines (x : R) (a : A) :
    ρ a * regularTraceAverage b ρ τ x = regularTraceAverage b ρ τ x * τ a := by
  let dual := d
  have hcoeff (i j : I) : dual.repr (dual i * a) j = b.repr (a * b j) i := by
    rw [repr_eq_trace b (a * b j) i,
      show dual = d from rfl, LinearMap.BilinForm.dualBasis_repr_apply]
    change regularTrace K A (dual i * a * b j) = regularTrace K A (a * b j * dual i)
    rw [mul_assoc, regularTrace_mul_comm K A (dual i) (a * b j)]
  calc
    _ = ∑ i, ρ (a * b i) * x * τ (dual i) := by
      simp only [regularTraceAverage, Finset.mul_sum, map_mul, mul_assoc]
      rfl
    _ = ∑ i, ∑ j, b.repr (a * b i) j • (ρ (b j) * x * τ (dual i)) := by
      apply Finset.sum_congr rfl
      intro i _
      conv_lhs => arg 1; arg 1; arg 2; rw [← b.sum_repr (a * b i)]
      simp only [map_sum, map_smul, Finset.sum_mul, smul_mul_assoc]
    _ = ∑ j, ∑ i, dual.repr (dual j * a) i • (ρ (b j) * x * τ (dual i)) := by
      rw [Finset.sum_comm]
      simp only [hcoeff]
    _ = ∑ j, ρ (b j) * x * τ (dual j * a) := by
      apply Finset.sum_congr rfl
      intro j _
      conv_rhs => arg 2; arg 2; rw [← dual.sum_repr (dual j * a)]
      simp only [map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
    _ = _ := by
      simp only [regularTraceAverage, Finset.sum_mul, map_mul, mul_assoc]
      rfl

/-- Averaging fixes an element that already intertwines the actions. -/
theorem regularTraceAverage_eq_of_intertwines (x : R) (hx : ∀ a, ρ a * x = x * τ a) :
    regularTraceAverage b ρ τ x = x := by
  calc
    _ = ∑ i, ρ (b i * d i) * x := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_assoc, ← hx (d i), ← mul_assoc, ← map_mul]
    _ = x := by rw [← Finset.sum_mul, ← map_sum, sum_basis_mul_dual, map_one, one_mul]

/-- The averaging construction commutes with changes of the target algebra. -/
theorem map_regularTraceAverage (f : R →ₐ[K] S) (x : R) :
    f (regularTraceAverage b ρ τ x) =
      regularTraceAverage b (f.comp ρ) (f.comp τ) (f x) := by
  simp only [regularTraceAverage, map_sum, map_mul, AlgHom.comp_apply]

/-- Averaging a projection onto an invariant image preserves its image. -/
theorem regularTraceAverage_same_image (p : R)
    (hp : ∀ a, p * (ρ a * p) = ρ a * p) :
    p * regularTraceAverage b ρ ρ p = regularTraceAverage b ρ ρ p ∧
      regularTraceAverage b ρ ρ p * p = p := by
  constructor
  · simp only [regularTraceAverage, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc p, hp]
  · calc
      regularTraceAverage b ρ ρ p * p = ∑ i, ρ (b i * d i) * p := by
        simp only [regularTraceAverage, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        simp only [mul_assoc, hp, map_mul]
      _ = p := by rw [← Finset.sum_mul, ← map_sum, sum_basis_mul_dual, map_one, one_mul]

/-- A surjective algebra map induces a surjection on the commutants of the
specified simple-algebra action and its image. -/
theorem exists_commuting_lift_of_surjective (f : R →ₐ[K] S) (hf : Function.Surjective f)
    (e : S) (he : ∀ a, f (ρ a) * e = e * f (ρ a)) :
    ∃ x : R, f x = e ∧ ∀ a, ρ a * x = x * ρ a := by
  classical
  obtain ⟨x, hx⟩ := hf e
  let b := Module.finBasis K A
  refine ⟨regularTraceAverage b ρ ρ x, ?_, regularTraceAverage_intertwines b ρ ρ x⟩
  rw [map_regularTraceAverage, hx]
  exact regularTraceAverage_eq_of_intertwines b (f.comp ρ) (f.comp ρ) e he

end Langlands.Algebra
