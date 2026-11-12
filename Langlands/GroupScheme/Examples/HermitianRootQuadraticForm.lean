import Langlands.GroupScheme.Examples.HermitianRootReflectionAction
import Langlands.GroupScheme.Examples.SU3RootParametersRational
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # The base-field quadratic form of a diagonal Hermitian form -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.HermitianRoot.DiagonalForm

open SU3Root

variable (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {ι : Type w} [Fintype ι]
  (H : DiagonalForm (fieldInvolution k L) ι)

local instance : FiniteDimensional k L :=
  .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two k L]; decide)

/-- The self-pairing as an extension-valued quadratic map over the base field. -/
def extensionQuadraticMap : QuadraticMap k (ι → L) L :=
  ∑ i, H.weight i • QuadraticMap.linMulLin
    (LinearMap.proj i : (ι → L) →ₗ[k] L)
    ((conjugation k L).toLinearMap.comp (LinearMap.proj i))

@[simp] theorem extensionQuadraticMap_apply (x : ι → L) :
    H.extensionQuadraticMap k L x = H.pairing x x := by
  simp [extensionQuadraticMap, QuadraticMap.linMulLin_apply, pairing,
    mul_assoc]

/-- A trace-one retraction to the base field, valid also in characteristic two. -/
def traceOneRetraction : L →ₗ[k] k :=
  (Algebra.trace k L).comp (LinearMap.mulLeft k (traceOne k L))

theorem algebraMap_traceOneRetraction (x : L) (hx : conjugation k L x = x) :
    algebraMap k L (traceOneRetraction k L x) = x := by
  change algebraMap k L (Algebra.trace k L (traceOne k L * x)) = x
  rw [algebraMap_trace, map_mul, hx, ← add_mul, traceOne_add_conjugate, one_mul]

/-- The actual quadratic form over the base field whose value is the Hermitian self-pairing. -/
def quadraticForm : QuadraticForm k (ι → L) :=
  (traceOneRetraction k L).compQuadraticMap (H.extensionQuadraticMap k L)

theorem algebraMap_quadraticForm (x : ι → L) :
    algebraMap k L (H.quadraticForm k L x) = H.pairing x x := by
  change algebraMap k L (traceOneRetraction k L (H.extensionQuadraticMap k L x)) = _
  rw [extensionQuadraticMap_apply]
  exact algebraMap_traceOneRetraction k L _ (H.bar_pairing x x)

@[simp] theorem quadraticForm_eq_zero_iff (x : ι → L) :
    H.quadraticForm k L x = 0 ↔ H.pairing x x = 0 := by
  rw [← H.algebraMap_quadraticForm k L x]
  exact (map_eq_zero_iff (algebraMap k L) (FaithfulSMul.algebraMap_injective k L)).symm

/-- Hermitian anisotropy is exactly anisotropy of the actual base-field quadratic form. -/
theorem quadraticForm_anisotropic_iff :
    (H.quadraticForm k L).Anisotropic ↔ H.IsAnisotropic := by
  simp only [QuadraticMap.Anisotropic, IsAnisotropic, H.quadraticForm_eq_zero_iff k L]

omit [Algebra.IsSeparable k L] in
/-- The underlying base-field dimension is twice the Hermitian dimension. -/
theorem quadraticForm_finrank :
    Module.finrank k (ι → L) = 2 * Fintype.card ι := by
  rw [Module.finrank_pi_fintype]
  simp [Algebra.IsQuadraticExtension.finrank_eq_two, mul_comm]

/-- The quadratic polar form is the sum of the two Hermitian cross-pairings. -/
theorem algebraMap_quadraticForm_polar (x y : ι → L) :
    algebraMap k L ((H.quadraticForm k L).polarBilin x y) =
      H.pairing x y + H.pairing y x := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, map_sub,
    H.algebraMap_quadraticForm, pairing_add_left, pairing_add_right]
  ring

/-- Nonzero Hermitian weights give a nonsingular quadratic polar form in every characteristic. -/
theorem quadraticForm_polar_separatingLeft (hw : ∀ i, H.weight i ≠ 0) :
    (H.quadraticForm k L).polarBilin.SeparatingLeft := by
  classical
  intro x hx
  funext i
  by_contra hi
  have ha : H.weight i * x i ≠ 0 := mul_ne_zero (hw i) hi
  let y : ι → L :=
    Pi.single i (conjugation k L ((H.weight i * x i)⁻¹ * traceOne k L))
  have hp : H.pairing x y = traceOne k L := by
    have hs (z : L) :
        H.pairing x (Pi.single i z) = H.weight i * x i * conjugation k L z := by
      simp [pairing, Pi.single_apply, apply_ite]
    rw [show H.pairing x y = H.weight i * x i *
      conjugation k L (conjugation k L ((H.weight i * x i)⁻¹ * traceOne k L)) from hs _,
      conjugation_involutive, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  have hp' : H.pairing y x = conjugation k L (traceOne k L) := by
    rw [← H.bar_pairing x y, hp]
    rfl
  have hpol : algebraMap k L ((H.quadraticForm k L).polarBilin x y) = 1 := by
    rw [H.algebraMap_quadraticForm_polar, hp, hp']
    exact traceOne_add_conjugate k L
  have hz := congrArg (algebraMap k L) (hx y)
  rw [map_zero] at hz
  exact one_ne_zero (hpol.symm.trans hz)

end Langlands.GroupScheme.HermitianRoot.DiagonalForm
