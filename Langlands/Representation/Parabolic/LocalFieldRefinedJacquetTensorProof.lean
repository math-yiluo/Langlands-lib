import Langlands.Representation.Parabolic.LocalFieldRefinedJacquetTensorStatement
import Langlands.AllField.Representation.Parabolic.RefinedInductionTensorNormalization

/-! Upper normalized Jacquet restriction of a tensor product inside a matrix Levi. -/

noncomputable section

namespace Langlands.RefinedJacquetTensor

open GeneralLinear Geometric

universe uF uV

variable {F : Type uF} [Field F] (T : LocalFieldData F) {n : ℕ}
  (B : BlockShape n) (S : BlockRefinement B)
  (A : ∀ i, Rep.{uV} ℂ (GeneralLinear (B.size i) F))

/-- The refined quotient, as coinvariants of the product of the inner unipotent
subgroups, is the tensor of the factor parabolic Jacquet carriers. -/
private def productQuotientEquiv :
    RefinedJacquetModule B S (FiniteTensor.external fun i => (A i).ρ) ≃ₗ[ℂ]
      PiTensorProduct ℂ (fun i => (S i).JacquetModule (A i).ρ) :=
  (RefinedOppositeJacquetTensor.coinvariantsEquiv (fun i => (A i).ρ)
      (fun i => (S i).unipotentSubgroup F)).trans
    (PiTensorProduct.congr fun i => ((S i).jacquetModuleEquiv (A i).ρ).symm)

/-- The comparison sends the class of a pure tensor to the tensor of the classes. -/
private theorem productQuotientEquiv_mk (v : ∀ i, A i) :
    productQuotientEquiv B S A
        (refinedJacquetMk B S _ (PiTensorProduct.tprod ℂ v)) =
      PiTensorProduct.tprod ℂ (fun i => (S i).jacquetMk (A i).ρ (v i)) := by
  change PiTensorProduct.congr _
      (RefinedOppositeJacquetTensor.coinvariantsEquiv _ _
        (Jacquet.mk _ _ (PiTensorProduct.tprod ℂ v))) = _
  rw [RefinedOppositeJacquetTensor.coinvariantsEquiv_mk_tprod,
    PiTensorProduct.congr_tprod]
  simp_rw [← BlockShape.jacquetModuleEquiv_mk, LinearEquiv.symm_apply_apply]

/-- The refined inverse half-modulus is the product of the inner inverse halves. -/
private theorem inverseHalf_eq_prod (m : refinedLevi F B S) :
    T.refinedLeviInverseHalfModulus B S m =
      ∏ i, (T.leviHalfModulus (S i) (LocalFieldData.refinedLeviBlock B S i m))⁻¹ := by
  change (T.refinedLeviHalfModulus B S m)⁻¹ = _
  rw [T.refinedLeviHalfModulus_eq_prod, Finset.prod_inv_distrib]

/-- The inverse refined Levi coordinates embed back to the original diagonal blocks. -/
private theorem blockEmbedding (m : refinedLevi F B S) (i : Fin B.length) :
    (S i).leviEmbedding F ((refinedLeviEquiv F B S).symm m i) = m.val i :=
  congrArg Subtype.val (((S i).leviEquiv F).apply_symm_apply (refinedLeviEval F B S i m))

/-- Equivariance of the comparison on the class of a pure tensor. -/
private theorem productQuotientEquiv_comm (m : refinedLevi F B S) (v : ∀ i, A i) :
    productQuotientEquiv B S A
        (T.normalizedRefinedJacquet B S (FiniteTensor.external fun i => (A i).ρ) m
          (refinedJacquetMk B S _ (PiTensorProduct.tprod ℂ v))) =
      FiniteTensor.external (fun i => T.normalizedJacquet (S i) (A i).ρ)
          ((refinedLeviEquiv F B S).symm m)
        (productQuotientEquiv B S A (refinedJacquetMk B S _ (PiTensorProduct.tprod ℂ v))) := by
  rw [T.normalizedRefinedJacquet_mk, FiniteTensor.external_tprod, map_smul,
    productQuotientEquiv_mk, productQuotientEquiv_mk, FiniteTensor.external_tprod]
  simp_rw [T.normalizedJacquet_mk_eq_inv_halfModulus, Units.smul_def]
  rw [MultilinearMap.map_smul_univ, inverseHalf_eq_prod T B S m, Units.coe_prod]
  simp_rw [blockEmbedding B S]
  rfl

/-- The refined Jacquet quotient is the external tensor of the factor quotients. -/
theorem localFieldRefinedJacquetTensor : LocalFieldRefinedJacquetTensorStatement.{uF, uV} := by
  intro F _ T n B S A
  refine ⟨⟨Representation.Equiv.mk (productQuotientEquiv B S A) ?_, ?_⟩⟩
  · intro m
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Jacquet.mk_surjective (FiniteTensor.external fun i => (A i).ρ)
      (refinedUnipotent F B S) x
    induction y using PiTensorProduct.induction_on with
    | smul_tprod a v =>
      simp only [LinearMap.comp_apply, map_smul]
      exact congrArg (a • ·) (productQuotientEquiv_comm T B S A m v)
    | add x y hx hy =>
      simp only [LinearMap.comp_apply, map_add] at hx hy ⊢
      rw [hx, hy]
  · exact productQuotientEquiv_mk B S A

end Langlands.RefinedJacquetTensor
