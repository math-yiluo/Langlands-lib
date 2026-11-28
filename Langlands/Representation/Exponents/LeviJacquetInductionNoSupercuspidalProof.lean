import Langlands.Representation.Geometric.RepresentedGeometricLemmaProof
import Langlands.Representation.Exponents.LeviInductionNoSupercuspidalSubquotientProof
import Langlands.Representation.Exponents.LeviJacquetNonSupercuspidalReduction

/-! # Non-supercuspidal subquotients for nonconjugate Levis -/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

/-- Renard VI.5.3(ii) for represented parabolics, from the geometric lemma and VI.5.2. -/
theorem leviJacquetInductionNoSupercuspidal :
    LeviJacquetInductionNoSupercuspidalStatement.{u, v} :=
  leviJacquetInductionNoSupercuspidal_of_geometricLemma representedGeometricLemma
    leviInductionNoSupercuspidalSubquotient

end Langlands.Aubert.General.RepresentedParabolic
