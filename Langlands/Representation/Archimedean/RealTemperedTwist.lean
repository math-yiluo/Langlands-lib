import Langlands.Representation.Archimedean.RealLinkedJacquetInStagesProof
import Langlands.Representation.Archimedean.RealTemperedIrreducibleStatement

/-!
# Determinant twists of real standard modules

Multiplication by `|det|^s` identifies the `O(n)`-finite real standard modules
before and after adding the real number `s` to every block exponent. It
intertwines `O(n)` and changes each real Lie operator by a scalar.
-/

noncomputable section

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealTemperedTwist

open Langlands.LocalFactor.Archimedean
open InductionStages RealLinkedJacquetStages

variable {n : ℕ}

/-- Multiplication by `|det|^s`, with inverse multiplication by `|det|^(-s)`. -/
def twistEquiv (s : ℝ) (ds : List RealBlock) (hr : realRank ds = n) :
    KFin n ds ≃ₗ[ℂ] KFin n (ds.map (realBlockTwist s)) where
  toLinearMap := twK (twist_char s hr) (twist_ind s ds)
  invFun := twK (untwist_char s hr) (untwist_ind s ds)
  left_inv f := by
    apply Subtype.ext
    funext g
    change detPow n (-s : ℝ) g *
      (detPow n s g * (f : Langlands.GeneralLinear n ℝ → ℂ) g) =
        (f : Langlands.GeneralLinear n ℝ → ℂ) g
    rw [← mul_assoc, ← detPow_add]
    simp [detPow_zero]
  right_inv f := by
    apply Subtype.ext
    funext g
    change detPow n s g *
      (detPow n (-s : ℝ) g * (f : Langlands.GeneralLinear n ℝ → ℂ) g) =
        (f : Langlands.GeneralLinear n ℝ → ℂ) g
    rw [← mul_assoc, ← detPow_add]
    simp [detPow_zero]

theorem twistEquiv_apply (s : ℝ) (ds : List RealBlock) (hr : realRank ds = n)
    (f : KFin n ds) (g : Langlands.GeneralLinear n ℝ) :
    (twistEquiv s ds hr f : Langlands.GeneralLinear n ℝ → ℂ) g =
      detPow n s g * (f : Langlands.GeneralLinear n ℝ → ℂ) g :=
  rfl

theorem twistEquiv_symm_apply (s : ℝ) (ds : List RealBlock) (hr : realRank ds = n)
    (f : KFin n (ds.map (realBlockTwist s))) (g : Langlands.GeneralLinear n ℝ) :
    ((twistEquiv s ds hr).symm f : Langlands.GeneralLinear n ℝ → ℂ) g =
      detPow n (-s : ℝ) g * (f : Langlands.GeneralLinear n ℝ → ℂ) g :=
  rfl

/-- The twist is trivial on `O(n)`. -/
theorem twistEquiv_rep (s : ℝ) (ds : List RealBlock) (hr : realRank ds = n)
    (k : Matrix.unitaryGroup (Fin n) ℝ) (f : KFin n ds) :
    twistEquiv s ds hr (realStandardRep n ds k f) =
      realStandardRep n (ds.map (realBlockTwist s)) k (twistEquiv s ds hr f) := by
  apply Subtype.ext
  funext g
  change detPow n s g * (f : Langlands.GeneralLinear n ℝ → ℂ) (g * Unitary.toUnits k) =
    detPow n s (g * Unitary.toUnits k) *
      (f : Langlands.GeneralLinear n ℝ → ℂ) (g * Unitary.toUnits k)
  rw [detPow_mul,
    detPow_of_mem_unitaryCompact (k := Unitary.toUnits k) _ k.2, mul_one]

/-- A multiplicative smooth determinant power has logarithmic derivative constant
on right translates. No explicit trace formula is needed. -/
theorem rightDerivative_detPow (s : ℂ) (X : Matrix (Fin n) (Fin n) ℝ)
    (g : Langlands.GeneralLinear n ℝ) :
    rightDerivative (matrixModel ℝ n) X (detPow n s) g =
      detPow n s g *
        rightDerivative (matrixModel ℝ n) X (detPow n s) (1 : Langlands.GeneralLinear n ℝ) := by
  have h := rightDerivative_mul_left_of_eq (contMDiff_detPow s)
    (a := g) (c := detPow n s g) (fun h => detPow_mul s g h) X 1
  rwa [mul_one] at h

/-- The real Lie action changes by the scalar logarithmic derivative of `|det|^s`. -/
theorem twistEquiv_lie (s : ℝ) (ds : List RealBlock) (hr : realRank ds = n)
    (X : Matrix (Fin n) (Fin n) ℝ) (f : KFin n ds) :
    realStandardLie n (ds.map (realBlockTwist s)) (1 ⊗ₜ X) (twistEquiv s ds hr f) =
      twistEquiv s ds hr (realStandardLie n ds (1 ⊗ₜ X) f) +
        rightDerivative (matrixModel ℝ n) X (detPow n (s : ℂ))
          (1 : Langlands.GeneralLinear n ℝ) • twistEquiv s ds hr f := by
  apply Subtype.ext
  funext g
  rw [realStandardLie_one_tmul_apply_coe]
  change rightDerivative (matrixModel ℝ n) X
    (fun g => detPow n (s : ℂ) g * (f : Langlands.GeneralLinear n ℝ → ℂ) g) g = _
  rw [RealPrincipalSeriesDuality.rightDerivative_mul_fun (contMDiff_detPow _)
    (contMDiff_of_mem_realStandardModule f.2.1), rightDerivative_detPow]
  change _ = detPow n s g *
    (realStandardLie n ds (1 ⊗ₜ X) f : Langlands.GeneralLinear n ℝ → ℂ) g +
      _ * (detPow n s g * (f : Langlands.GeneralLinear n ℝ → ℂ) g)
  rw [realStandardLie_one_tmul_apply_coe]
  ring

end RealTemperedTwist

end Langlands.Archimedean
