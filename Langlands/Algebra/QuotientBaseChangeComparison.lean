import Langlands.Algebra.QuotientBaseChangeComparisonStatement

/-! # Proof of the canonical quotient base-change comparison -/

universe u v w

open scoped TensorProduct

namespace Langlands.Algebra

noncomputable section

/-- The canonical quotient maps become bijective when the extended ideals agree. -/
theorem quotientBaseChangeComparison : QuotientBaseChangeComparisonStatement.{u, v, w} := by
  intro R B T _ _ _ _ _ I J hIJ hmap
  let eI := Algebra.TensorProduct.quotientTensorEquiv (R := R) R T B I
  let eJ := Algebra.TensorProduct.quotientTensorEquiv (R := R) R T B J
  let e := (eI.trans (Ideal.quotientEquivAlgOfEq R hmap)).trans eJ.symm
  have he : Algebra.TensorProduct.map (Ideal.Quotient.factorₐ R hIJ) (AlgHom.id R T) =
      e.toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro x t
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [e, eI, eJ]
  have hright : Function.Bijective
      (Algebra.TensorProduct.map (Ideal.Quotient.factorₐ R hIJ) (AlgHom.id R T)) := by
    rw [he]
    exact e.bijective
  refine ⟨hright, ?_⟩
  apply (LinearMap.lTensor_bij_iff_rTensor_bij T
    (Ideal.Quotient.factorₐ R hIJ).toLinearMap).mpr
  exact hright

end

end Langlands.Algebra
