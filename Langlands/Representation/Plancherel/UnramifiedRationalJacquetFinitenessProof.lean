import Langlands.Representation.Plancherel.UnramifiedRationalJacquetStructuralReduction
import Langlands.Representation.Exponents.ArbitraryParabolicFiniteSupportReduction
import Langlands.GroupScheme.Rational.ParabolicDoubleCosetAssembly
import Langlands.GroupScheme.Rational.RationalBruhatProof
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyProof
import Langlands.GroupScheme.Rational.ParabolicIntersectionCentralizerProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.BruhatTits.Parabolic.QuotientCompactProof

/-! # Native Jacquet finiteness for the actual universal induced supercuspidal family

Renard 2026, VI.9.2 (printed pp.198–199 / PDF pp.204–205): the published
structural reduction, with both of its global structural premises discharged
by published proofs.
-/

noncomputable section

namespace Langlands.Plancherel

universe u uV

/-- Renard VI.9.2: every compact-open fixed module of every output normalized
Jacquet action of the actual universal induced supercuspidal family is finite
over the complete rational-norm algebra. -/
theorem rationalSupercuspidalJacquetFamilyFinite :
    RationalSupercuspidalJacquetFamilyFiniteStatement.{u, uV} :=
  rationalSupercuspidalJacquetFamilyFinite_of_structural
    (GroupScheme.representedParabolicDoubleCosetStatement_of_dynamic_structural_inputs
      GroupScheme.rationalBruhat GroupScheme.genericMinimalParabolic
      GroupScheme.minimalParabolicConjugacy GroupScheme.parabolicIntersectionCentralizer
      GroupScheme.parabolicDynamic GroupScheme.smoothMaximalSplitTorusConjugacy)
    (by
      intro k _ _ _ _ _ G hG
      let := hG.isAffineHom
      intro _ _ P p hp
      exact Aubert.General.RepresentedParabolic.compactSpace_leftQuotient_pointImage_of_dynamic
        GroupScheme.parabolicDynamic BruhatTits.dynamicParabolicQuotientCompact hG p hp)

end Langlands.Plancherel
