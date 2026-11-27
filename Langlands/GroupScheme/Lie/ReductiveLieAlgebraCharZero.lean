import Langlands.GroupScheme.Lie.SemisimpleLieAlgebraCharZeroProof

/-! # The Lie algebra of a connected reductive group in characteristic zero is reductive -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry LieAlgebra
open scoped TensorProduct

namespace Langlands.GroupScheme.Lie

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Reductivity of the Lie algebra.** Over a field of characteristic zero, the actual
dual-number tangent Lie algebra of a connected reductive group has its radical equal to its
centre. -/
theorem hasCentralRadical_of_isConnectedReductive {k : Type u} [Field k] [CharZero k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G) :
    letI := instAffineKernelLieRing (R := CommRingCat.of k) (A := k) G
    letI := instAffineKernelLieAlgebra (R := CommRingCat.of k) (A := k) G
    HasCentralRadical k (Additive (lieKernel G k)) := by
  let := instAffineKernelLieRing (R := CommRingCat.of k) (A := k) G
  let := instAffineKernelLieAlgebra (R := CommRingCat.of k) (A := k) G
  let := hG.smooth
  let := hG.connectedSpace
  exact hasCentralRadical_of_radical_le _ _
    (radical_le_center_of_hasTrivialUnipotentRadical hG.hasTrivialUnipotentRadical)

end Langlands.GroupScheme.Lie
