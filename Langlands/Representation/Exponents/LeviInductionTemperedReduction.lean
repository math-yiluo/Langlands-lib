import Langlands.Representation.Exponents.LeviInductionNormalizedTemperedStatement
import Langlands.Representation.Exponents.GeometricLemmaTemperedCone
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityStatement
import Langlands.GroupScheme.Rational.ParabolicRootPresentationStatement
import Langlands.GroupScheme.Rational.RelativeRootNegationProof

/-! # Parabolic induction preserves temperedness, from four structural inputs

This internal reduction assembles Renard VII.2.2 for represented parabolics from the
represented geometric lemma, Jacquet admissibility, compactness of the parabolic
quotients and existence of parabolic root presentations. It does not prove any of
these four inputs.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The exact VII.2.2 proposition follows from the represented geometric lemma,
preservation of admissibility by the normalized Jacquet functors, compactness of the
actual parabolic quotients and existence of compatible root presentations. -/
def LeviInductionTemperedReductionStatement : Prop :=
  RepresentedGeometricLemmaStatement.{u, v} →
    ArbitraryParabolicJacquetAdmissibilityStatement.{u, v} →
      ArbitraryParabolicQuotientCompactStatement.{u} →
        ParabolicRootPresentationExistenceStatement.{u} →
          LeviInductionNormalizedTemperedStatement.{u, v}

/-- Conditional assembly of VII.2.2. Admissibility of the induced representation comes
from quotient compactness. For each parabolic triple of `G`, presentation existence
gives the nonempty presentation clause, and the cone clause is
`normalizedRealPart_mem_nonnegCone_of_isGluedFrom`, fed with the geometric lemma, the
proved negation stability of relative roots and Jacquet admissibility for `M`. -/
theorem leviInductionNormalizedTempered_reduction :
    LeviInductionTemperedReductionStatement.{u, v} := by
  intro hGL hJ hcompact hexists k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro σ hσ
  refine ⟨leviInductionFunctor_obj_isAdmissible_of_quotientCompactStatement hcompact hG
    p l r hp hl hr hmul σ hσ.isAdmissible, ?_⟩
  intro Q L A q lQ a hq hlQ ha
  refine ⟨hexists k G hG Q L A q lQ a hq hlQ ha, ?_⟩
  intro pres V rQ hrQ hmulQ χ hχ
  obtain ⟨m, -, z, -, D, hD⟩ :=
    hGL k G hG P M U Q L V p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  have hneg := relativeRootNegation k G hG _ pres.data.i pres.isCompatible.maximalSplit
  refine normalizedRealPart_mem_nonnegCone_of_isGluedFrom p l r hp hr hl hmul
    q lQ rQ hq hrQ hlQ hmulQ D hD ha pres hneg σ hσ ?_ χ hχ
  intro i
  let := leviPointTopology (D i).l' (D i).hl'
  exact isAdmissible_comp_continuousMulEquiv _ (leviPointsEquiv (D i).p' (D i).l' (D i).hp'
    (D i).hl') (hJ k M hl.isConnectedReductive _ _ _ (D i).p' (D i).l' (D i).r' (D i).hp'
      (D i).hl' (D i).hr' (D i).hmul' σ hσ.isAdmissible)

end Langlands.Aubert.General.RepresentedParabolic
