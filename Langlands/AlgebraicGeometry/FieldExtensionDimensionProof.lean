import Langlands.AlgebraicGeometry.FieldExtensionDimensionStatement
import Langlands.AlgebraicGeometry.FlatIntegralPureDimensionProof
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Dimension comparisons under field extension -/

universe u v w

open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

open P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen

theorem finiteTypeFieldExtensionRingDimensionInvariance :
    FiniteTypeFieldExtensionRingDimensionInvariance.{u,v,w} := by
  intro k K A _ _ _ _ _ _
  cases subsingleton_or_nontrivial A
  · simp only [ringKrullDim_eq_bot_of_subsingleton]
  · obtain ⟨n, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
    let f := Algebra.TensorProduct.map (AlgHom.id k K) g
    have hf_inj : Function.Injective f := by
      exact Module.Flat.lTensor_preserves_injective_linearMap g.toLinearMap hinj
    have hf_fin : f.toRingHom.Finite :=
      RingHom.Finite.tensorProductMap (f := AlgHom.id k K) (g := g)
        (RingHom.Finite.id K) hfin
    have hA := ringKrullDim_eq_of_ringHom_isIntegral_of_injective
      g.toRingHom hfin.to_isIntegral hinj
    have hKA := ringKrullDim_eq_of_ringHom_isIntegral_of_injective
      f.toRingHom hf_fin.to_isIntegral hf_inj
    rw [← hA, ← hKA,
      ringKrullDim_eq_of_ringEquiv (MvPolynomial.algebraTensorAlgEquiv k K).toRingEquiv,
      ringKrullDim_mvPolynomial_fin, ringKrullDim_mvPolynomial_fin]

theorem algebraicFieldExtensionPureRingDimensionInvariance :
    AlgebraicFieldExtensionPureRingDimensionInvariance.{u,v,w} := by
  intro k K A _ _ _ _ _ _ d
  have hinj : Function.Injective (algebraMap A (A ⊗[k] K)) := by
    convert (TensorProduct.comm k K A).injective.comp
      (Module.Flat.tensorProduct_mk_injective (R := k) (S := K) (M := A)) using 1
    ext a
    simp
  have : FaithfulSMul A (A ⊗[k] K) :=
    (faithfulSMul_iff_algebraMap_injective A (A ⊗[k] K)).mpr hinj
  exact flatIntegralPureRingDimensionInvariance A (A ⊗[k] K) d

theorem fieldExtensionDimensionComparisons :
    FieldExtensionDimensionComparisons.{u,v,w} :=
  ⟨finiteTypeFieldExtensionRingDimensionInvariance,
    algebraicFieldExtensionPureRingDimensionInvariance⟩

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
