import Langlands.Geometry.Analytic.AffineAnalytificationParametricEvaluation
import Langlands.Geometry.Analytic.AffineAnalytificationSemilinearPoints
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Scalar automorphisms on points of an affine base change -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.AffineAnalytification

open Topology
open scoped TensorProduct

variable {k : Type u} [Field k] (K : Type v) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] [Algebra k K] (A : Type w) [CommRing A] [Algebra k A]

/-- The ring map on the actual algebraic base change is the scalar automorphism on the first
factor and the identity on the original algebra. -/
def tensorCoefficientMap (σ : K ≃ₐ[k] K) : (K ⊗[k] A) →+* (K ⊗[k] A) :=
  (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k A)).toRingHom

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- Scalar automorphisms act on a simple tensor by acting on its scalar factor. -/
@[simp] theorem tensorCoefficientMap_tmul (σ : K ≃ₐ[k] K) (c : K) (a : A) :
    tensorCoefficientMap K A σ (c ⊗ₜ a) = σ c ⊗ₜ a :=
  Algebra.TensorProduct.map_tmul σ.toAlgHom (AlgHom.id k A) c a

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The base changed algebra map acts semilinearly over the scalar automorphism. -/
theorem tensorCoefficientMap_scalar (σ : K ≃ₐ[k] K) (c : K) :
    tensorCoefficientMap K A σ (algebraMap K (K ⊗[k] A) c) = algebraMap K (K ⊗[k] A) (σ c) :=
  tensorCoefficientMap_tmul K A σ c 1

variable (P : FinitePolynomialPresentation K (K ⊗[k] A))

/-- The point map induced by a norm-preserving coefficient automorphism of the affine
base change. -/
def tensorCoefficientPointMap (σ : K ≃ₐ[k] K) (hσ : ∀ c, ‖σ c‖ = ‖c‖) :
    C(Space K P, Space K P) :=
  semilinearBaseMap K P P σ.toRingHom hσ (tensorCoefficientMap K A σ)
    (tensorCoefficientMap_scalar K A σ)

variable {T : Type z} [TopologicalSpace T] (σ : T → K ≃ₐ[k] K)
  (hnorm : ∀ t c, ‖σ t c‖ = ‖c‖) (hcont : ∀ c : K, Continuous (fun t => σ t c))

include hcont in
private theorem continuous_tensorCoefficientPointMap_eval (a : K ⊗[k] A) :
    Continuous (fun p : T × Space K P =>
      pointSeminorm K P (tensorCoefficientPointMap K A P (σ p.1) (hnorm p.1) p.2) a) := by
  obtain ⟨n, c, b, rfl⟩ := TensorProduct.exists_sum_tmul_eq a
  let d : Fin n → K ⊗[k] A := fun i => (1 : K) ⊗ₜ b i
  let r : Fin n → T → K := fun i t => σ t (c i)
  have h := continuous_pointSeminorm_sum K P Finset.univ d r (fun i _ => hcont (c i))
  convert h using 1
  funext p
  change pointSeminorm K P (semilinearBaseMap K P P (σ p.1).toRingHom (hnorm p.1)
    (tensorCoefficientMap K A (σ p.1)) (tensorCoefficientMap_scalar K A (σ p.1)) p.2)
      (∑ i, c i ⊗ₜ b i) = _
  calc
    _ = pointSeminorm K P p.2 (tensorCoefficientMap K A (σ p.1) (∑ i, c i ⊗ₜ b i)) :=
      pointSeminorm_semilinearBaseMap K P P (σ p.1).toRingHom (hnorm p.1)
        (tensorCoefficientMap K A (σ p.1)) (tensorCoefficientMap_scalar K A (σ p.1)) p.2 _
    _ = _ := by
      congr 1
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [tensorCoefficientMap_tmul, d, r, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.algebraMap_self_apply, mul_one, one_mul]

/-- The induced point map is continuous jointly in the automorphism parameter and the point
when every scalar orbit is norm-continuous. Each tensor has a finite simple-tensor expression. -/
def tensorCoefficientPointEvaluation : C(T × Space K P, Space K P) :=
  ⟨fun p => tensorCoefficientPointMap K A P (σ p.1) (hnorm p.1) p.2,
    (SeminormComparison.isEmbedding_pointSeminorm K P).continuous_iff.2 <|
      continuous_pi fun a => continuous_tensorCoefficientPointMap_eval K A P σ hnorm hcont a⟩

end Langlands.Analytic.AffineAnalytification
