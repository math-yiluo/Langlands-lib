import Langlands.GroupScheme.Examples.SU3RootParametersRational
import Langlands.GroupScheme.Examples.SU3RootParametersMatrix

noncomputable section
open scoped TensorProduct
open Algebra

namespace Langlands.GroupScheme.SU3Root

universe u v w w'

variable (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
  [IsQuadraticExtension k L] [Algebra.IsSeparable k L]

section TestAlgebra

variable (R : Type w) [CommRing R] [Algebra k R]

/-- The upper triangular embedding on the actual quadratic tensor parameters. -/
def tensorEmbedding : tensorParameters k L R →*
    Matrix.GeneralLinearGroup (Fin 3) (R ⊗[k] L) :=
  Parameters.embedding (tensorInvolution k L R)

theorem tensorEmbedding_entries (x : tensorParameters k L R) :
    (tensorEmbedding k L R x : Matrix (Fin 3) (Fin 3) (R ⊗[k] L)) =
      !![1, x.first, x.second; 0, 1, tensorConjugation k L R x.first; 0, 0, 1] := rfl

theorem tensorEmbedding_injective : Function.Injective (tensorEmbedding k L R) :=
  Parameters.embedding_injective (tensorInvolution k L R)

@[simp] theorem tensorEmbedding_det (x : tensorParameters k L R) :
    Matrix.GeneralLinearGroup.det (tensorEmbedding k L R x) = 1 :=
  Parameters.embedding_det x

theorem tensorEmbedding_upperUnipotent (x : tensorParameters k L R) :
    IsUpperUnipotent
      (tensorEmbedding k L R x : Matrix (Fin 3) (Fin 3) (R ⊗[k] L)) :=
  Parameters.matrix_upperUnipotent x

theorem tensorEmbedding_preservesForm (x : tensorParameters k L R) :
    PreservesForm (tensorInvolution k L R)
      (tensorEmbedding k L R x : Matrix (Fin 3) (Fin 3) (R ⊗[k] L)) :=
  Parameters.matrix_preservesForm x

theorem mem_range_tensorEmbedding
    (g : Matrix.GeneralLinearGroup (Fin 3) (R ⊗[k] L)) :
    g ∈ (tensorEmbedding k L R).range ↔
      IsUpperUnipotent (g : Matrix (Fin 3) (Fin 3) (R ⊗[k] L)) ∧
        PreservesForm (tensorInvolution k L R)
          (g : Matrix (Fin 3) (Fin 3) (R ⊗[k] L)) :=
  Parameters.mem_range_embedding g

end TestAlgebra

section Naturality

variable {R : Type w} {S : Type w'} [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]

/-- Changing the actual tensor coefficient algebra commutes with the matrix embedding. -/
theorem tensorEmbedding_map (f : R →ₐ[k] S) (x : tensorParameters k L R) :
    tensorEmbedding k L S (tensorParametersMap k L f x) =
      Matrix.GeneralLinearGroup.map (tensorCoefficientMap k L f).toRingHom
        (tensorEmbedding k L R x) :=
  Parameters.embedding_map (tensorCoefficientMap k L f).toRingHom
    (tensorCoefficientMap_bar k L f) x

end Naturality

/-- The rational tensor identification also commutes with the matrix embedding. -/
theorem rationalEmbedding_compatible (x : tensorParameters k L k) :
    Parameters.embedding (fieldInvolution k L) (rationalParametersEquiv k L x) =
      Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.lid k L).toRingHom
        (tensorEmbedding k L k x) :=
  Parameters.embedding_map (Algebra.TensorProduct.lid k L).toRingHom
    (rationalTensor_bar k L) x

end Langlands.GroupScheme.SU3Root
