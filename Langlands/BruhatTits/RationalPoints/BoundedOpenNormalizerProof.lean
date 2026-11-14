import Langlands.BruhatTits.RationalPoints.BoundedOpenNormalizerReduction
import Langlands.BruhatTits.RationalPoints.AdjointNormKernelBoundedPreimage
import Langlands.BruhatTits.RationalPoints.DenseBoundedNormalizerAdjointProof

/-! # Bounded open-subgroup normalizers in the rational common norm kernel -/

noncomputable section
universe u

open AlgebraicGeometry

namespace Langlands.BruhatTits.RationalPoints

/-- KP Proposition 2.2.16 over nonarchimedean local fields, for the actual
normalizer and common rational-character norm kernel. -/
theorem boundedOpenNormalizer : BoundedOpenNormalizerStatement.{u} := by
  apply boundedOpenNormalizer_of_adjoint_inputs denseBoundedNormalizerAdjoint
  intro F _ _ _ _ G hG A q hq
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffineHom A.X.hom :=
    hq.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  exact isAlgebraicallyBounded_adjoint_preimage_inter_normKernel G hG A q hq

end Langlands.BruhatTits.RationalPoints
