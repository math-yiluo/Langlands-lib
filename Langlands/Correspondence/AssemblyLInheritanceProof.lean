import Langlands.Correspondence.AssemblyLParameterPairs
import Langlands.Representation.RankinSelberg.SquareIntegrableDataLFactorReduction
import Langlands.Representation.RankinSelberg.SegmentHeadLFactorReduction
import Langlands.Representation.RankinSelberg.SquareIntegrableLFactorProof
import Langlands.Representation.RankinSelberg.TemperedLFactorProof
import Langlands.Representation.RankinSelberg.LanglandsTypeLFactorProof
import Langlands.Representation.Classification.SquareIntegrableEqualExponentGroupingProof
import Langlands.Representation.Classification.RegularLanglandsDataUniquenessProof

/-!
# Pair L-factor inheritance for the assembled correspondence

The assembly of a supercuspidal correspondence is compatible with pair L-factors
(Henniart 2002, Theorem 1.5(iii), L part, and §2.8–2.9). The proof combines the
reduction `assemblyLInheritance_of_rankinSelberg` with the published proofs of its
two representation-side premises: JPSS (9.5) for square-integrable Langlands data
and Henniart's segment-head L formula.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Henniart's segment-head L formula at the universes of the assembled classes,
from JPSS (8.2) for square-integrable pairs in both orders. -/
theorem assemblySegmentHeadLFactor :
    RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA} :=
  RankinSelberg.segmentHeadLFactor_of_squareIntegrable
    RankinSelberg.squareIntegrableLFactor RankinSelberg.squareIntegrableLFactor

/-- JPSS (9.5) for square-integrable Langlands data at the universes of the
assembled classes, from equal-exponent grouping, the tempered and Langlands-type
L-factor formulas, and uniqueness of ordered tempered Langlands data. -/
theorem assemblySquareIntegrableDataLFactor :
    RankinSelberg.SquareIntegrableDataLFactorStatement.{uF, uA, uA} :=
  RankinSelberg.squareIntegrableDataLFactor_of_prerequisites
    (fun _ _ F => Classification.squareIntegrableEqualExponentGrouping F _)
    (fun _ _ F => Classification.squareIntegrableEqualExponentGrouping F _)
    RankinSelberg.temperedLFactor RankinSelberg.langlandsTypeLFactor
    glRegularLanglandsDataUniqueness glRegularLanglandsDataUniqueness

/-- Pair L-factor inheritance: the assembly of a supercuspidal correspondence is
compatible with pair L-factors for every nontrivial additive character. -/
theorem assemblyLInheritance : AssemblyLInheritanceStatement.{uF, uP, uA} F :=
  assemblyLInheritance_of_rankinSelberg F assemblySquareIntegrableDataLFactor
    assemblySegmentHeadLFactor

end Langlands.Correspondence
