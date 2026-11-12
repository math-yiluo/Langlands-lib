import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityReduction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof

/-! # Admissibility of the actual normalized Jacquet module: proof

Renard 2026, VI.6.1 Corollary (printed pp.176–177 / PDF pp.182–183),
normalized clause, for every represented parabolic.
-/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.6.1 Corollary: the actual normalized Jacquet functor of every
represented parabolic preserves admissibility. -/
theorem arbitraryParabolicJacquetAdmissibility :
    ArbitraryParabolicJacquetAdmissibilityStatement.{u, v} :=
  arbitraryParabolicJacquetAdmissibility_of_dynamic parabolicDynamic
    dynamicGeometricUnipotentRadical

end Langlands.Aubert.General.RepresentedParabolic
