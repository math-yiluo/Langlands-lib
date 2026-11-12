import Langlands.Representation.Exponents.LeviJacquetCuspidalReduction
import Langlands.Representation.Geometric.RepresentedGeometricLemmaProof

/-! # Renard VI.5.3 (i) for represented parabolics: proof -/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

/-- Renard VI.5.3, Proposition (i): if no Levi subgroup of an actual parabolic of `L` is
conjugate to `M`, the normalized Jacquet module along `Q = LU` of the induction from
`P = MN` of a supercuspidal representation of `M(F)` vanishes. -/
theorem leviJacquetInductionVanishing : LeviJacquetInductionVanishingStatement.{u, v} :=
  leviJacquetInductionVanishing_of_geometricLemma representedGeometricLemma

end Langlands.Aubert.General.RepresentedParabolic
