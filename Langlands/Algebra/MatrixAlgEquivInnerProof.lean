import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Langlands.Algebra.MatrixAlgEquivInnerStatement

/-! Field-linear automorphisms of full matrix algebras are inner (proof),
and the comparison of two matrix charts of an algebra is inner. -/

namespace Langlands.MatrixAlgebra

universe uk uI uB

/-- Every `k`-algebra automorphism `e` of `Matrix I I k` is conjugation by a unit.
The proof transports Mathlib's `AlgEquiv.eq_linearEquivConjAlgEquiv` along
`LinearMap.toMatrixAlgEquiv'`. -/
theorem exists_unit_conj_of_algEquiv {k : Type uk} [Field k] {I : Type uI} [Fintype I]
    [DecidableEq I] (e : Matrix I I k ≃ₐ[k] Matrix I I k) :
    ∃ U : (Matrix I I k)ˣ, ∀ M : Matrix I I k,
      e M = (U : Matrix I I k) * M * ((U⁻¹ : (Matrix I I k)ˣ) : Matrix I I k) := by
  let ψ : Module.End k (I → k) ≃ₐ[k] Matrix I I k := LinearMap.toMatrixAlgEquiv'
  obtain ⟨T, hT⟩ := ((ψ.trans e).trans ψ.symm).eq_linearEquivConjAlgEquiv
  let U : (Matrix I I k)ˣ :=
    { val := ψ T.toLinearMap
      inv := ψ T.symm.toLinearMap
      val_inv := by
        rw [← map_mul, ← map_one ψ]
        congr 1
        ext x
        simp
      inv_val := by
        rw [← map_mul, ← map_one ψ]
        congr 1
        ext x
        simp }
  refine ⟨U, fun M => ?_⟩
  have h := congrArg (fun g => ψ (g (ψ.symm M))) hT
  simp only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
    LinearEquiv.conjAlgEquiv_apply] at h
  rw [h, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, map_mul, map_mul,
    AlgEquiv.apply_symm_apply, ← mul_assoc]
  rfl

/-- `Langlands.MatrixAlgebra.AlgEquivIsInnerStatement` holds. -/
theorem algEquivIsInner : AlgEquivIsInnerStatement.{uk, uI} :=
  fun _ _ _ _ _ e => exists_unit_conj_of_algEquiv e

/-- Two `k`-algebra charts `φ ψ : B ≃ₐ[k] Matrix I I k` of the same algebra differ by
conjugation by a unit: `ψ b = U * φ b * U⁻¹` for every `b : B`. -/
theorem exists_unit_conj_of_charts {k : Type uk} [Field k] {I : Type uI} [Fintype I]
    [DecidableEq I] {B : Type uB} [Semiring B] [Algebra k B] (φ ψ : B ≃ₐ[k] Matrix I I k) :
    ∃ U : (Matrix I I k)ˣ, ∀ b : B,
      ψ b = (U : Matrix I I k) * φ b * ((U⁻¹ : (Matrix I I k)ˣ) : Matrix I I k) := by
  obtain ⟨U, hU⟩ := exists_unit_conj_of_algEquiv (φ.symm.trans ψ)
  exact ⟨U, fun b => by simpa using hU (φ b)⟩

end Langlands.MatrixAlgebra
