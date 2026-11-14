import Langlands.Representation.Aubert.General.CanonicalRationalComplexTargets
import Langlands.Representation.Aubert.General.RationalCorrectedFiltrationTargets
import Langlands.Representation.Aubert.General.RationalInducedWeylConjugacyTarget
import Langlands.Representation.Aubert.General.PrerequisiteStatements
import Langlands.Representation.CuspidalSupport.RationalWholeCuspidalDecompositionStatement

/-! # Reductions of the canonical Sharp targets of Corollaire 3.9

Five implication statements on the canonical actual rational-point families.
Each one says that a canonical target about the terminal cokernel `E#`
follows from named published targets: Renard VI.3.5 (whole-category cuspidal
splitting), corrected graded vanishing, the two dynamic finite-length targets
(Renard VI.6.2, VI.6.4) and induced K0 Weyl conjugacy (Aubert (1.2)). No
proof is supplied here.
-/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- Reduction of retention of the support type by the canonical actual
terminal cokernel to the whole-category cuspidal decomposition of Renard
VI.3.5 at carrier universe `max (u + 1) v`. No proof is supplied. -/
def CanonicalRationalSharpSupportRetentionReductionStatement : Prop :=
  CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v} →
    CanonicalRationalSharpSupportRetentionStatement.{u, v}

/-- Reduction of finite length of the canonical actual terminal cokernel to
the two dynamic finite-length targets (Renard VI.6.2, VI.6.4) at carrier
universe `max (u + 1) v`. No proof is supplied. -/
def CanonicalRationalSharpFiniteLengthReductionStatement : Prop :=
  DynamicInductionFiniteLengthStatement.{u, max (u + 1) v} →
    DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v} →
      CanonicalRationalSharpFiniteLengthStatement.{u, v}

/-- Reduction of Corollaire 3.9 (b) (irreducibility of `E#` on the cuspidal
series) for the canonical actual families to five published targets: Renard
VI.3.5 at carrier universe `max (u + 1) v`, corrected graded vanishing, the
two dynamic finite-length targets and induced K0 Weyl conjugacy. No proof is
supplied. -/
def CanonicalRationalSharpIrreducibleReductionStatement : Prop :=
  CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v} →
    RationalCorrectedGradedVanishingStatement.{u, v} →
      DynamicInductionFiniteLengthStatement.{u, max (u + 1) v} →
        DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v} →
          RationalInducedK0WeylConjugacyStatement.{u, v} →
            CanonicalRationalSharpIrreducibleStatement.{u, v}

/-- Reduction of retention of the cuspidal series by `E#`, up to an associated
standard Levi, for the canonical actual families to the same five inputs as
the irreducibility reduction. No proof is supplied. -/
def CanonicalRationalSharpCuspidalSeriesReductionStatement : Prop :=
  CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v} →
    RationalCorrectedGradedVanishingStatement.{u, v} →
      DynamicInductionFiniteLengthStatement.{u, max (u + 1) v} →
        DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v} →
          RationalInducedK0WeylConjugacyStatement.{u, v} →
            CanonicalRationalSharpCuspidalSeriesStatement.{u, v}

/-- Reduction of Corollaire 3.9 (c) (`(E#)# ≅ E` on the cuspidal series) for
the canonical actual families to the same five inputs as the irreducibility
reduction. No proof is supplied. -/
def CanonicalRationalSharpInvolutionReductionStatement : Prop :=
  CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v} →
    RationalCorrectedGradedVanishingStatement.{u, v} →
      DynamicInductionFiniteLengthStatement.{u, max (u + 1) v} →
        DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v} →
          RationalInducedK0WeylConjugacyStatement.{u, v} →
            CanonicalRationalSharpInvolutionStatement.{u, v}

end Langlands.Aubert.General.RationalPointFamily
