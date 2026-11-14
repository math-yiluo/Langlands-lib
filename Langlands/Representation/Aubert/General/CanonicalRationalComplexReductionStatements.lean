import Langlands.Representation.Aubert.General.CanonicalRationalComplexTargets
import Langlands.Representation.Aubert.General.RationalCorrectedFiltrationTargets
import Langlands.Representation.CuspidalSupport.RationalWholeCuspidalDecompositionStatement

/-! # Reductions of canonical corrected Theorem 3.6, the associated-Levi comparison and the Sharp class formula

Three implication statements on the canonical actual rational-point families.
Each one says that a canonical main target follows from Renard VI.3.5
(whole-category cuspidal splitting) and the corrected graded vanishing target,
or from the latter alone. No proof is supplied here.
-/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- Reduction of corrected Theorem 3.6 (erratum, p.4687) for the canonical
actual complex to two published targets: the whole-category cuspidal
decomposition of Renard VI.3.5 at carrier universe `max (u + 1) v`, and
vanishing of the non-standard graded pieces of the corrected support
filtration. No proof is supplied. -/
def CanonicalRationalCorrectedTheorem36ReductionStatement : Prop :=
  CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v} →
    RationalCorrectedGradedVanishingStatement.{u, v} →
      CanonicalRationalCorrectedTheorem36Statement.{u, v}

/-- Reduction of display (**) of the erratum (p.4690), the associated-Levi
Jacquet comparison for the canonical actual families, to vanishing of the
non-standard graded pieces of the corrected support filtration. No proof is
supplied. -/
def CanonicalRationalAssociatedLeviComparisonReductionStatement : Prop :=
  RationalCorrectedGradedVanishingStatement.{u, v} →
    CanonicalRationalAssociatedLeviComparisonStatement.{u, v}

/-- Reduction of the signed class formula (Aubert 1995, Corollaire 3.9 (a),
extended to finite-length members of `Alg({I})` by the 1996 erratum) for the
canonical actual families to the same two inputs as the corrected Theorem 3.6
reduction. No proof is supplied. -/
def CanonicalRationalSharpClassFormulaReductionStatement : Prop :=
  CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v} →
    RationalCorrectedGradedVanishingStatement.{u, v} →
      CanonicalRationalSharpClassFormulaStatement.{u, v}

end Langlands.Aubert.General.RationalPointFamily
