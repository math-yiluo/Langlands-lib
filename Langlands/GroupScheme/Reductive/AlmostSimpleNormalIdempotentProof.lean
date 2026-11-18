import Langlands.GroupScheme.Reductive.AlmostSimpleNormalIdempotentStatement
import Langlands.GroupScheme.Reductive.IdempotentImage

/-! # Normal idempotents of almost-simple field groups -/

universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The exact normal-idempotent dichotomy for almost-simple field groups. -/
theorem almostSimpleNormalIdempotent :
    AlmostSimpleNormalIdempotentStatement.{u} := by
  intro k _ G hG ψ hidem hn
  exact hG.normal_idempotent_eq_zero_or_id ψ hidem hn

end Langlands.GroupScheme
