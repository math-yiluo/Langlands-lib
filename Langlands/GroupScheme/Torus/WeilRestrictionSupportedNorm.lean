import Langlands.GroupScheme.Torus.WeilRestrictionNormCoordinates

/-! # Inclusion-supported points and their rational norms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.WeilGm

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  {I : Type u} [Fintype I] [DecidableEq I]
  (E : I → IntermediateField k L)

attribute [local instance] Classical.propDecidable

/-- A tensor unit with a prescribed value at each inclusion embedding and value one elsewhere. -/
def inclusionSupportedTensorUnit (b : I → Lˣ) : ((∀ i, E i) ⊗[k] L)ˣ :=
  (productTensorEmbeddingUnitsEquiv k L E).symm
    (fun i => Pi.mulSingle (E i).val (b i))

@[simp] theorem inclusionSupportedTensorUnit_coordinate (b : I → Lˣ)
    (i : I) (τ : E i →ₐ[k] L) :
    productTensorEmbeddingUnitsEquiv k L E
        (inclusionSupportedTensorUnit k L E b) i τ =
      (Pi.mulSingle (E i).val (b i) : (E i →ₐ[k] L) → Lˣ) τ := by
  simp [inclusionSupportedTensorUnit]

/-- Evaluation of the algebra decomposition agrees with the corresponding unit coordinate. -/
theorem productTensorEmbeddingUnitsEquiv_val
    (x : ((∀ i, E i) ⊗[k] L)ˣ) (i : I) (τ : E i →ₐ[k] L) :
    ((productTensorEmbeddingUnitsEquiv k L E x i τ : Lˣ) : L) =
      productTensorEmbeddingEquiv k L E (x : (∀ i, E i) ⊗[k] L) i τ := rfl

/-- Inclusion of a rational unit is evaluated by each field embedding. -/
theorem productTensorEmbeddingEquiv_includeLeft (a : ∀ i, E i)
    (i : I) (τ : E i →ₐ[k] L) :
    productTensorEmbeddingEquiv k L E
        ((Algebra.TensorProduct.includeLeft :
          (∀ i, E i) →ₐ[k] (∀ i, E i) ⊗[k] L) a) i τ = τ (a i) := by
  change productTensorEmbeddingEquiv k L E (a ⊗ₜ (1 : L)) i τ = _
  simp

/-- The corresponding point of the actual base-changed Weil restriction. -/
def inclusionSupportedPoint (b : I → Lˣ) :
    rationalPoints (GaloisPointComparison.baseChanged k L
      (groupScheme (CommRingCat.of k) (∀ i, E i))) :=
  (extensionUnitsEquiv k L (∀ i, E i)).symm
    (inclusionSupportedTensorUnit k L E b)

local instance : IsAffine (commGroupScheme (CommRingCat.of k) (∀ i, E i)).X.left := by
  change IsAffine (Spec _)
  infer_instance

/-- In each factor, the descended rational norm of an inclusion-supported point is
the relative field norm of its prescribed coordinate. -/
theorem rationalNorm_inclusionSupportedPoint (b : I → Lˣ) (i : I) :
    (MulEquiv.piUnits (rationalUnitsEquiv k (∀ i, E i)
      (GaloisPointComparison.rationalNorm k L
        (commGroupScheme (CommRingCat.of k) (∀ i, E i))
        (inclusionSupportedPoint k L E b)))) i =
      Units.map (Algebra.norm (E i)) (b i) := by
  apply Units.ext
  apply (E i).val.injective
  have h := congrArg
    (fun x : ((∀ i, E i) ⊗[k] L)ˣ =>
      productTensorEmbeddingEquiv k L E x.val i (E i).val)
    (rationalNorm_tensor k L (∀ i, E i) (inclusionSupportedPoint k L E b))
  change (E i).val _ = _
  calc
    _ = ∏ σ : L ≃ₐ[k] L,
        productTensorEmbeddingEquiv k L E
          (Algebra.TensorProduct.lTensor (S := (∀ i, E i))
            (∀ i, E i) σ.toAlgHom
            (inclusionSupportedTensorUnit k L E b).val) i (E i).val := by
      simpa [productTensorEmbeddingEquiv_includeLeft, inclusionSupportedPoint] using h
    _ = ∏ σ : L ≃ₐ[k] L,
        if σ.symm.toAlgHom.comp (E i).val = (E i).val then σ (b i : L) else 1 := by
      apply Finset.prod_congr rfl
      intro σ _
      rw [productTensorEmbeddingEquiv_conjugate]
      rw [← productTensorEmbeddingUnitsEquiv_val,
        inclusionSupportedTensorUnit_coordinate]
      by_cases hσ : σ.symm.toAlgHom.comp (E i).val = (E i).val
      · simp [hσ]
      · simp [hσ]
    _ = _ := prod_automorphisms_single k L (E i) (b i : L)

end Langlands.GroupScheme.WeilGm
