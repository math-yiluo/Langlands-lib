import Langlands.Representation.CuspidalSupport.SupercuspidalCoefficientCriterionReduction
import Langlands.BruhatTits.SpecialCompact.JointBasisProof

/-! # Renard VI.2.1, Theorem, (a) ⇔ (b): proof

A smooth complex representation of `G(F)` is supercuspidal if and only if its matrix
coefficients against smooth dual vectors have support compact modulo the centre.
The proof applies `supercuspidalCoefficientCriterionReduction` to
`jointSpecialCompactBasisExistence`. -/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

/-- Renard VI.2.1, Theorem, (a) ⇔ (b): for every nonarchimedean local field `k`, connected
reductive `G` over `k` and smooth complex representation `A` of `G(k)`, `A` is
supercuspidal if and only if each matrix coefficient of `A` against a smooth dual vector
has support in `C · Z` for a compact `C`, where `Z` is the centre of `G(k)`. -/
theorem supercuspidalCoefficientCriterion :
    SupercuspidalCoefficientCriterionStatement.{u, v} :=
  supercuspidalCoefficientCriterionReduction
    Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence

end Langlands.Aubert.General.RepresentedParabolic
