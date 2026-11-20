import Langlands.GroupScheme.HomScheme.SquareZeroCohomology
import Langlands.GroupScheme.Torus.SeparatedNormalizerStatement
import Langlands.GroupScheme.Torus.TorusNormalizerInfinitesimalLifting

/-! # Proof of the separated torus normalizer statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The normalizer of a closed relative torus in a smooth group scheme is
represented by a smooth closed subgroup scheme. The separatedness and
quasi-compactness hypotheses of the statement are not used. -/
theorem separatedTorusNormalizer : SeparatedTorusNormalizerStatement.{u} := by
  intro S G hG _ _ A t hA ht
  let := hG
  let N := relativeTorusSmoothNormalizerModel_of_squareZeroCohomology
    HomScheme.squareZeroHomomorphismCohomology t hA ht
  exact ⟨N.1.group, N.1.hom, N.1.closed, N.2, N.1.represents⟩

end Langlands.GroupScheme
