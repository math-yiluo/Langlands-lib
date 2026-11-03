import Langlands.LinearAlgebra.RationalSpan
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Rational spans and kernels detected after real scalar extension -/

noncomputable section

open TensorProduct

namespace Langlands.LinearAlgebra.RationalSpan

variable (M : Type*) [AddCommGroup M]

/-- Reassociate successive rational and real scalar extensions of a lattice. -/
def rationalRealEquiv : ℝ ⊗[ℚ] (ℚ ⊗[ℤ] M) ≃ₗ[ℝ] ℝ ⊗[ℤ] M :=
  AlgebraTensorModule.cancelBaseChange ℤ ℚ ℝ ℝ M

@[simp] theorem rationalRealEquiv_tmul (r : ℝ) (q : ℚ) (m : M) :
    rationalRealEquiv M (r ⊗ₜ[ℚ] (q ⊗ₜ[ℤ] m)) = ((q : ℝ) * r) ⊗ₜ[ℤ] m := rfl

/-- The rational-linear map from a rationalized lattice to its real scalar
extension, compatible with the standard tensor generators. -/
def toReal : (ℚ ⊗[ℤ] M) →ₗ[ℚ] (ℝ ⊗[ℤ] M) :=
  ((rationalRealEquiv M).toLinearMap.restrictScalars ℚ).comp
    (TensorProduct.mk ℚ ℝ (ℚ ⊗[ℤ] M) 1)

@[simp] theorem toReal_tmul (q : ℚ) (m : M) :
    toReal M (q ⊗ₜ[ℤ] m) = (q : ℝ) ⊗ₜ[ℤ] m := by
  simp only [toReal, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    TensorProduct.mk_apply, LinearEquiv.coe_coe, rationalRealEquiv_tmul, mul_one]

@[simp] theorem toReal_toRat (m : M) :
    toReal M (toRat m) = (1 : ℝ) ⊗ₜ[ℤ] m := by
  simp only [toRat_apply, toReal_tmul, Rat.cast_one]

/-- The transition from rational to real tensors is injective, even when the
original additive group has torsion. -/
theorem toReal_injective : Function.Injective (toReal M) :=
  (rationalRealEquiv M).injective.comp
    (Module.Flat.tensorProduct_mk_injective (R := ℚ) (S := ℝ)
      (M := ℚ ⊗[ℤ] M))

/-- A subspace's real extension contains a rational generator exactly when the
original rational subspace contains it. -/
theorem one_tmul_mem_baseChange_iff {P : Type*} [AddCommGroup P] [Module ℚ P]
    (W : Submodule ℚ P) (x : P) :
    (1 : ℝ) ⊗ₜ[ℚ] x ∈ W.baseChange ℝ ↔ x ∈ W := by
  have h := Submodule.baseChange_le_iff (A := ℝ)
    (p := Submodule.span ℚ {x}) (q := W)
  simpa only [Submodule.baseChange_span, Set.image_singleton,
    Submodule.span_singleton_le_iff_mem, TensorProduct.mk_apply] using h

/-- Successive extension of a rational span is the real span of the original
integer tensor generators. -/
theorem map_ratSpan_baseChange (R : Set M) :
    ((ratSpan R).baseChange ℝ).map (rationalRealEquiv M).toLinearMap =
      Submodule.span ℝ ((fun m : M => (1 : ℝ) ⊗ₜ[ℤ] m) '' R) := by
  rw [ratSpan, Submodule.baseChange_span, Submodule.map_span,
    Set.image_image, Set.image_image]
  change Submodule.span ℝ
    ((fun m : M => rationalRealEquiv M (1 ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] m))) '' R) = _
  simp only [rationalRealEquiv_tmul, Rat.cast_one, one_mul]

/-- Real-span membership reflects exactly to rational-span membership for a
vector from the rationalized lattice. -/
theorem toReal_mem_span_iff (R : Set M) (x : ℚ ⊗[ℤ] M) :
    toReal M x ∈ Submodule.span ℝ ((fun m : M => (1 : ℝ) ⊗ₜ[ℤ] m) '' R) ↔
      x ∈ ratSpan R := by
  rw [← map_ratSpan_baseChange M R, Submodule.mem_map_equiv]
  change (rationalRealEquiv M).symm
    (rationalRealEquiv M ((1 : ℝ) ⊗ₜ[ℚ] x)) ∈ (ratSpan R).baseChange ℝ ↔ _
  rw [LinearEquiv.symm_apply_apply, one_tmul_mem_baseChange_iff]

variable {M} {N : Type*} [AddCommGroup N]

/-- Rational-to-real transition commutes with scalar extension of every
integer-linear map. -/
theorem toReal_baseChange (f : M →ₗ[ℤ] N) (x : ℚ ⊗[ℤ] M) :
    toReal N (f.baseChange ℚ x) = f.baseChange ℝ (toReal M x) := by
  induction x using TensorProduct.inductionOn with
  | tmul q m => simp only [LinearMap.baseChange_tmul, toReal_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Equality of an actual real scalar-extension kernel with a root-generated
span descends to the full rationalized lattice. -/
theorem ker_baseChange_rat_eq_ratSpan_of_real (f : M →ₗ[ℤ] N) (R : Set M)
    (hreal : (f.baseChange ℝ).ker =
      Submodule.span ℝ ((fun m : M => (1 : ℝ) ⊗ₜ[ℤ] m) '' R)) :
    (f.baseChange ℚ).ker = ratSpan R := by
  ext x
  rw [LinearMap.mem_ker, ← toReal_mem_span_iff M R x, ← hreal, LinearMap.mem_ker,
    ← toReal_baseChange]
  constructor
  · intro hx
    rw [hx, map_zero]
  · intro hx
    exact toReal_injective N (hx.trans (map_zero (toReal N)).symm)

end Langlands.LinearAlgebra.RationalSpan
