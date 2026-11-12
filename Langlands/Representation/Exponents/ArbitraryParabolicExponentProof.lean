import Langlands.Representation.Exponents.ArbitraryParabolicExponentReduction
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityReduction
import Langlands.Representation.Exponents.ArbitraryParabolicFiniteSupportReduction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof
import Langlands.BruhatTits.Parabolic.QuotientCompactProof

/-! # Characteristic-space decompositions and exponents for represented parabolics: proof

Renard 2026, VII.1.1 (printed pp.220–221/PDF pp.226–227). The published conditional
assembly `arbitraryParabolicExponent_reduction` is applied to Jacquet admissibility and
quotient compactness, each obtained from its published dynamic reduction and the
published unconditional dynamic structure theorems.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.1.1: (VII.1.1.1) with finiteness in finite length, the `P = G` remark,
and parts (i) and (ii) of the lemma, for every represented parabolic of a connected
reductive group over a nonarchimedean local field. -/
theorem arbitraryParabolicExponent : ArbitraryParabolicExponentStatement.{u, v} :=
  arbitraryParabolicExponent_reduction
    (arbitraryParabolicJacquetAdmissibility_of_dynamic parabolicDynamic
      dynamicGeometricUnipotentRadical)
    (by
      intro k _ _ _ _ _ G hG
      have := hG.isAffineHom
      let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
      intro _ _ P p hp
      exact compactSpace_leftQuotient_pointImage_of_dynamic parabolicDynamic
        BruhatTits.dynamicParabolicQuotientCompact hG p hp)

end Langlands.Aubert.General.RepresentedParabolic
