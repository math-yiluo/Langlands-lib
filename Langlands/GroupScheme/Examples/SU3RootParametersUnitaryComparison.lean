import Langlands.GroupScheme.Examples.SU3RootParametersRealization
import Langlands.GroupScheme.Examples.QuasiSplitUnitary

noncomputable section
open scoped TensorProduct
open Algebra

namespace Langlands.GroupScheme.SU3Root

universe u
variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [IsQuadraticExtension k L] [Algebra.IsSeparable k L]

section TestAlgebra
variable (R : Type u) [CommRing R] [Algebra k R]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Tensor swap identifies the new convention with the existing unitary conjugation. -/
theorem tensorSwap_conjugation (x : R ⊗[k] L) :
    Algebra.TensorProduct.comm k R L ((tensorInvolution k L R).bar x) =
      QuasiSplitUnitary.scalarConjugation R (conjugation k L)
        (Algebra.TensorProduct.comm k R L x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The same involution expressed in the tensor convention of the existing unitary API. -/
def unitaryTensorInvolution : RingInvolution (L ⊗[k] R) where
  bar := (QuasiSplitUnitary.scalarConjugation R (conjugation k L)).toRingEquiv
  involutive := QuasiSplitUnitary.scalarConjugation_involutive R (conjugation k L)

/-- The coordinate group is unchanged by the choice of tensor-factor order. -/
def tensorSwapParametersEquiv :
    tensorParameters k L R ≃* Parameters (unitaryTensorInvolution k L R) :=
  Parameters.mapEquiv (Algebra.TensorProduct.comm k R L).toRingEquiv
    (tensorSwap_conjugation k L R)

@[simp] theorem tensorSwapParametersEquiv_first (x : tensorParameters k L R) :
    (tensorSwapParametersEquiv k L R x).first =
      Algebra.TensorProduct.comm k R L x.first := rfl

@[simp] theorem tensorSwapParametersEquiv_second (x : tensorParameters k L R) :
    (tensorSwapParametersEquiv k L R x).second =
      Algebra.TensorProduct.comm k R L x.second := rfl

/-- Reordering the tensor factors commutes with the three-by-three matrix realization. -/
theorem tensorSwap_embedding (x : tensorParameters k L R) :
    Parameters.embedding (unitaryTensorInvolution k L R) (tensorSwapParametersEquiv k L R x) =
      Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.comm k R L).toRingHom
        (tensorEmbedding k L R x) :=
  Parameters.embedding_map (c := tensorInvolution k L R) (d := unitaryTensorInvolution k L R)
    (Algebra.TensorProduct.comm k R L).toRingHom
    (tensorSwap_conjugation k L R) x

end TestAlgebra

section Coefficients
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

omit [IsQuadraticExtension k L] [Algebra.IsSeparable k L] in
/-- Coefficient change also agrees with the existing right-factor convention after tensor swap. -/
theorem tensorSwap_coefficientMap (f : R →ₐ[k] S) (x : R ⊗[k] L) :
    Algebra.TensorProduct.comm k S L (tensorCoefficientMap k L f x) =
      QuasiSplitUnitary.tensorCoefficientMap f (Algebra.TensorProduct.comm k R L x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Coefficients
end Langlands.GroupScheme.SU3Root
