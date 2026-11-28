import Langlands.Representation.CuspidalSupport.UniformAdmissibilityAssemblyReduction
import Langlands.Representation.CuspidalSupport.RationalPointsUniformAdmissibilityReduction
import Langlands.Representation.CuspidalSupport.SupercuspidalUniformSupportReduction
import Langlands.Representation.Aubert.General.IrreducibleAdmissibleOfDatum
import Langlands.Representation.Aubert.General.RationalJacquetCartanDatum
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.BruhatTits.SpecialCompact.JointBasisProof

/-! # Renard VI.2.3–VI.2.4: uniform admissibility and uniform support

This module proves `UniformAdmissibilityStatements`: the uniform admissibility
theorem for `G(F)` (Renard VI.2.3), its analogue for the common norm kernel `⁰G`
(the Remark after VI.2.3) and the common support, compact modulo the centre, of
the level-`K` coefficients of irreducible supercuspidal representations
(Renard VI.2.4). It composes the Library's conditional reductions of these
statements with the proofs of their structural premises. -/

namespace Langlands.CuspidalSupport

universe u v

open GroupScheme

/-- Renard VI.2.2 (every irreducible smooth complex representation of `G(F)` is
admissible), at every carrier universe, from the joint special-compact basis
through a Jacquet–Cartan datum on `G(F)`. -/
theorem rationalPointsIrreducibleAdmissible :
    Aubert.General.RationalPointsIrreducibleAdmissibleStatement.{u, v} :=
  Aubert.General.rationalPointsIrreducibleAdmissible_of_jacquetCartanDatum
    (Aubert.General.rationalPointsJacquetCartanDatum_of
      BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence standardCocharacter
      standardParabolicOrder)

/-- Renard VI.2.3, Theorem and Remark, and VI.2.4, Proposition: uniform admissibility
for `G(F)` and for `⁰G`, and a common open support, compact modulo the centre, of the
level-`K` coefficients of all irreducible supercuspidal representations. -/
theorem uniformAdmissibilityStatements : UniformAdmissibilityStatements.{u, v} :=
  uniformAdmissibilityAssemblyReduction.{u, v}
    (rationalPointsUniformAdmissibilityReduction.{u, max u v}
      BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence standardCocharacter
      relativeRootSystem rationalPointsIrreducibleAdmissible.{u, max u v})
    (supercuspidalUniformCoefficientSupportReduction.{u, v} parabolicDynamic
      standardCocharacter relativeRootSystem
      BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence)

end Langlands.CuspidalSupport
