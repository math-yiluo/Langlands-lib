import Langlands.Global.IntegralFiniteAdeleRationalization
import Langlands.Global.AdeleQuotientCompactProof
import Mathlib.RingTheory.Localization.BaseChange

noncomputable section

open scoped TensorProduct nonZeroDivisors

namespace Langlands.Global

/-- Rationalizing the actual integral finite adeles gives the finite adeles. -/
theorem integralFiniteAdeleRationalization : IntegralFiniteAdeleRationalization := by
  let i : integralFiniteAdeles ℚ →ₐ[ℤ] FiniteAdeles ℚ :=
    (integralFiniteAdeles ℚ).subtype.toIntAlgHom
  let f := i.toLinearMap
  have : IsLocalizedModule (nonZeroDivisors ℤ) f :=
    { map_units := fun s ↦ by
        rw [← (Algebra.lsmul ℤ (A := ℚ) ℤ (FiniteAdeles ℚ)).commutes]
        exact (IsLocalization.map_units ℚ s).map _
      surj := fun x ↦ by
        obtain ⟨d, hd, hx⟩ := exists_integer_mul_mem_adicCompletionIntegers x
        let n : ℤ := Rat.ringOfIntegersEquiv d
        have hn : n ≠ 0 := by
          exact (map_ne_zero_iff Rat.ringOfIntegersEquiv
            Rat.ringOfIntegersEquiv.injective).mpr hd
        have hi : n • x ∈ integralFiniteAdeles ℚ := by
          apply (mem_integralFiniteAdeles ℚ _).mpr
          intro v
          have hnq : (n : ℚ) = algebraMap (NumberField.RingOfIntegers ℚ) ℚ d :=
            Rat.ringOfIntegersEquiv_apply_coe d
          have hnloc : (n : FiniteCompletion ℚ v) =
              algebraMap (NumberField.RingOfIntegers ℚ) (FiniteCompletion ℚ v) d := by
            rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ℚ) ℚ,
              ← hnq, map_intCast]
          rw [zsmul_eq_mul]
          change (n : FiniteCompletion ℚ v) * x v ∈ v.adicCompletionIntegers ℚ
          rw [hnloc]
          exact hx v
        exact ⟨(⟨n • x, hi⟩, ⟨n, mem_nonZeroDivisors_iff_ne_zero.mpr hn⟩), rfl⟩
      exists_of_eq := fun h ↦ ⟨1, by
        have h' : (↑_ : FiniteAdeles ℚ) = ↑_ := h
        exact congrArg (fun a : integralFiniteAdeles ℚ ↦ (1 : nonZeroDivisors ℤ) • a)
          (Subtype.ext h')⟩ }
  let h := IsLocalizedModule.isBaseChange (nonZeroDivisors ℤ) ℚ f
  let g := AlgHom.liftEquiv ℤ ℚ (integralFiniteAdeles ℚ) (FiniteAdeles ℚ) i
  have he : g.toLinearMap = h.equiv.toLinearMap := by
    ext q a
    rfl
  have hg : Function.Bijective g := by
    change Function.Bijective g.toLinearMap
    rw [he]
    exact h.equiv.bijective
  refine ⟨AlgEquiv.ofBijective g hg, fun q a ↦ ?_⟩
  exact Algebra.smul_def q (a : FiniteAdeles ℚ)

end Langlands.Global
