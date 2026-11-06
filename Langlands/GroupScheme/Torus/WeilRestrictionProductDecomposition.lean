import Langlands.GroupScheme.Torus.WeilRestrictionNormCoordinates

/-! # Tensor coordinates for products of intermediate fields -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.WeilGm

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  {I : Type u} [Fintype I] [DecidableEq I] (E : I → IntermediateField k L)

/-- Uncurrying a family of coefficient functions as an algebra equivalence. -/
def productEmbeddingUncurry :
    (∀ i, (E i →ₐ[k] L) → L) ≃ₐ[L] ((Σ i, E i →ₐ[k] L) → L) where
  __ := (Equiv.piCurry fun i (_ : E i →ₐ[k] L) => L).symm
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The product tensor decomposition, with its two indices combined into one. -/
def productEmbeddingDecomposition :
    L ⊗[k] (∀ i, E i) ≃ₐ[L] ((Σ i, E i →ₐ[k] L) → L) :=
  ((Algebra.TensorProduct.piRight k L L (fun i => E i)).trans
    (AlgEquiv.piCongrRight fun i => separableEmbeddingDecomposition k (E i) L
      (intermediate_minpoly_splits k L (E i)))).trans
    (productEmbeddingUncurry k L E)

end Langlands.GroupScheme.WeilGm
