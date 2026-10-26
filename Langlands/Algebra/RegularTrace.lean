import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.RingTheory.SimpleRing.Basic

/-! # Regular trace and duality for simple algebras -/

universe u v

namespace Langlands.Algebra

section Ring

variable (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A]

/-- Trace of left multiplication on the underlying scalar module. -/
noncomputable def regularTrace : A →ₗ[R] R :=
  (LinearMap.trace R A).comp (_root_.Algebra.lmul R A).toLinearMap

@[simp] theorem regularTrace_apply (a : A) :
    regularTrace R A a = LinearMap.trace R A (LinearMap.mulLeft R a) := rfl

/-- Cyclicity holds even though the algebra need not be commutative. -/
theorem regularTrace_mul_comm (a b : A) :
    regularTrace R A (a * b) = regularTrace R A (b * a) := by
  simp only [regularTrace_apply, LinearMap.mulLeft_mul, ← Module.End.mul_eq_comp]
  exact LinearMap.trace_mul_comm R (LinearMap.mulLeft R a) (LinearMap.mulLeft R b)

/-- The regular trace of the product, as a bilinear form. -/
noncomputable def regularTraceForm : LinearMap.BilinForm R A :=
  LinearMap.compr₂ (LinearMap.mul R A) (regularTrace R A)

@[simp] theorem regularTraceForm_apply (a b : A) :
    regularTraceForm R A a b = regularTrace R A (a * b) := rfl

theorem regularTraceForm_isSymm : (regularTraceForm R A).IsSymm :=
  ⟨regularTrace_mul_comm R A⟩

/-- The radical of the regular trace pairing is a genuine two-sided ideal. -/
noncomputable def regularTraceRadical : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' {a | ∀ b, regularTrace R A (a * b) = 0}
    (by intro b; simp)
    (by intro a b ha hb c; simp [add_mul, map_add, ha c, hb c])
    (by intro a ha b; simp [neg_mul, map_neg, ha b])
    (by
      intro a b hb c
      rw [mul_assoc, regularTrace_mul_comm R A a (b * c), mul_assoc]
      exact hb (c * a))
    (by intro a b ha c; simpa only [mul_assoc] using ha (b * c))

@[simp] theorem mem_regularTraceRadical (a : A) :
    a ∈ regularTraceRadical R A ↔ ∀ b, regularTrace R A (a * b) = 0 := by
  simp [regularTraceRadical]

end Ring

section Field

variable (K : Type u) (A : Type v) [Field K] [Ring A] [Algebra K A]
variable [FiniteDimensional K A]

@[simp] theorem regularTrace_one :
    regularTrace K A 1 = (Module.finrank K A : K) := by
  simp [regularTrace_apply, LinearMap.mulLeft_one]

variable [CharZero K] [IsSimpleRing A]

/-- Simplicity and characteristic zero force the radical to vanish. -/
theorem regularTraceRadical_eq_bot : regularTraceRadical K A = ⊥ := by
  apply (eq_bot_or_eq_top (regularTraceRadical K A)).resolve_right
  intro h
  have h1 : (1 : A) ∈ regularTraceRadical K A := by rw [h]; trivial
  have hz := (mem_regularTraceRadical K A 1).mp h1 1
  rw [one_mul, regularTrace_one] at hz
  exact (Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := K) (M := A)))) hz

/-- The regular trace pairing is nondegenerate on a finite-dimensional simple
algebra over a characteristic-zero field. -/
theorem regularTraceForm_nondegenerate : (regularTraceForm K A).Nondegenerate := by
  have hleft : (regularTraceForm K A).SeparatingLeft := by
    intro a ha
    have hmem : a ∈ regularTraceRadical K A :=
      (mem_regularTraceRadical K A a).mpr ha
    simpa [regularTraceRadical_eq_bot K A] using hmem
  refine ⟨hleft, ?_⟩
  intro a ha
  apply hleft a
  intro b
  rw [regularTraceForm_apply, regularTrace_mul_comm]
  exact ha b

/-- The duality map sends `a` to the functional `b ↦ Tr(L_(a*b))`. -/
noncomputable def regularTraceDual : A ≃ₗ[K] Module.Dual K A :=
  (regularTraceForm K A).toDual (regularTraceForm_nondegenerate K A)

@[simp] theorem regularTraceDual_apply (a b : A) :
    regularTraceDual K A a b = regularTrace K A (a * b) := rfl

/-- Left multiplication becomes the transpose of right multiplication under
regular-trace duality. -/
theorem regularTraceDual_conj_mulLeft (a : A) :
    (regularTraceDual K A).conj (LinearMap.mulLeft K a) =
      Module.Dual.transpose (LinearMap.mulRight K a) := by
  ext f b
  change regularTrace K A (a * (regularTraceDual K A).symm f * b) = f (b * a)
  rw [mul_assoc, regularTrace_mul_comm, mul_assoc]
  change regularTraceDual K A ((regularTraceDual K A).symm f) (b * a) = f (b * a)
  rw [LinearEquiv.apply_symm_apply]

/-- On a simple characteristic-zero algebra, left and right regular traces
coincide. This conclusion is not asserted for arbitrary algebras. -/
theorem trace_mulRight_eq_regularTrace (a : A) :
    LinearMap.trace K A (LinearMap.mulRight K a) = regularTrace K A a := by
  rw [← LinearMap.trace_transpose', ← regularTraceDual_conj_mulLeft K A a]
  exact LinearMap.trace_conj' _ _

end Field

end Langlands.Algebra
