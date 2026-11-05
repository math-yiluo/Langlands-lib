import Langlands.Global.AdelicFunctoriality.IntegralLocalComparisonProof

/-! # Completed-field tensor of the original number-field integral model coefficients -/

noncomputable section

universe u v

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct
  Langlands.Global.AdelicFunctoriality.FiniteExtension

namespace Langlands.Global.AdelicFunctoriality.IntegralModelFieldTensor

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  (p : HeightOneSpectrum (𝓞 K))

/-- The original lower integer action agrees with the completed-field embedding. -/
scoped instance (q : FinitePlacesAbove L p) :
    IsScalarTower (𝓞 K) (p.adicCompletion K) (q.1.adicCompletion L) :=
  .of_algebraMap_eq fun r => by
    change algebraMap (𝓞 K) (q.1.adicCompletion L) r =
      FiniteExtension.completionMap p q.1 (algebraMap (𝓞 K) (p.adicCompletion K) r)
    simpa only [IsScalarTower.algebraMap_apply (𝓞 K) K (p.adicCompletion K),
      IsScalarTower.algebraMap_apply (𝓞 K) K (q.1.adicCompletion L),
      IsScalarTower.algebraMap_apply K L (q.1.adicCompletion L)] using
      (FiniteExtension.completionMap_coe p q.1 (r : K)).symm

/-- The original integral coefficient algebra, tensored with the lower completed field. -/
def tensorMap :
    p.adicCompletion K ⊗[𝓞 K] (𝓞 L) →ₐ[p.adicCompletion K]
      (∀ q : FinitePlacesAbove L p, q.1.adicCompletion L) :=
  AlgHom.pi fun q => Algebra.TensorProduct.lift
    (Algebra.ofId (p.adicCompletion K) (q.1.adicCompletion L))
    (Algebra.algHom (𝓞 K) (𝓞 L) (q.1.adicCompletion L)) (fun _ _ => .all _ _)

@[simp]
theorem tensorMap_tmul (a : p.adicCompletion K) (b : 𝓞 L) (q : FinitePlacesAbove L p) :
    tensorMap (L := L) p (a ⊗ₜ[𝓞 K] b) q =
      FiniteExtension.completionMap p q.1 a * algebraMap (𝓞 L) (q.1.adicCompletion L) b := rfl

/-- The original field comparison is unchanged after exchanging the tensor factors. -/
theorem comparison_comm (z : p.adicCompletion K ⊗[𝓞 K] (𝓞 L)) :
    integralTensorComparison L p (TensorProduct.comm (𝓞 K) _ _ z) = tensorMap (L := L) p z := by
  induction z with
  | tmul a b =>
    funext q
    rw [TensorProduct.comm_tmul, integralTensorComparison_tmul, tensorMap_tmul, mul_comm]
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add]

/-- The published actual field comparison proves bijectivity without another approximation argument. -/
theorem tensorMap_bijective : Function.Bijective (tensorMap (L := L) p) := by
  have hf : (tensorMap (L := L) p : _ → _) =
      integralTensorComparison L p ∘ TensorProduct.comm (𝓞 K) (p.adicCompletion K) (𝓞 L) := by
    funext z
    exact (comparison_comm p z).symm
  rw [hf]
  exact (integralLocalTensorComparison K L p).1.comp (TensorProduct.comm _ _ _).bijective

/-- The actual field tensor equivalence retains the original integral model coefficient ring. -/
def tensorEquiv :
    p.adicCompletion K ⊗[𝓞 K] (𝓞 L) ≃ₐ[p.adicCompletion K]
      (∀ q : FinitePlacesAbove L p, q.1.adicCompletion L) :=
  AlgEquiv.ofBijective (tensorMap p) (tensorMap_bijective p)

@[simp]
theorem tensorEquiv_tmul (a : p.adicCompletion K) (b : 𝓞 L) (q : FinitePlacesAbove L p) :
    tensorEquiv (L := L) p (a ⊗ₜ[𝓞 K] b) q =
      FiniteExtension.completionMap p q.1 a * algebraMap (𝓞 L) (q.1.adicCompletion L) b := rfl

@[simp]
theorem tensorEquiv_one_tmul (b : 𝓞 L) (q : FinitePlacesAbove L p) :
    tensorEquiv (L := L) p (1 ⊗ₜ[𝓞 K] b) q =
      algebraMap (𝓞 L) (q.1.adicCompletion L) b := by
  simp only [tensorEquiv_tmul, map_one, one_mul]

end Langlands.Global.AdelicFunctoriality.IntegralModelFieldTensor
