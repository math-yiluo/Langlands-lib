import Langlands.GroupScheme.Rational.AffineWeilParabolicElementaryReduction
import Langlands.GroupScheme.Rational.AffineWeilParabolicRadicalTransportProof

/-! # Parabolic radical generation under affine Weil restriction: proof -/

universe u

namespace Langlands.GroupScheme

/-- Finite separable affine Weil restriction preserves the subgroup generated
by rational points of geometric unipotent radicals of parabolic subgroups. -/
theorem affineWeilParabolicElementarySubgroup :
    AffineWeilParabolicElementarySubgroupStatement.{u} :=
  affineWeilParabolicElementarySubgroup_of_radicalTransport
    affineWeilParabolicRadicalTransport

end Langlands.GroupScheme
