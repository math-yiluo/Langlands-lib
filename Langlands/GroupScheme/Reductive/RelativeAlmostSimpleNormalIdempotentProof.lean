import Langlands.GroupScheme.Reductive.RelativeAlmostSimpleNormalIdempotentStatement
import Langlands.GroupScheme.Reductive.RestrictedNormalIdempotent
import Langlands.GroupScheme.Reductive.IdempotentProjectionInjective

/-! # Relative normal-idempotent rigidity for almost-simple fibres -/

universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The exact relative normal-idempotent rigidity statement, including
arbitrary coefficient rings and uniqueness of the base idempotent. -/
theorem relativeAlmostSimpleNormalIdempotent :
    RelativeAlmostSimpleNormalIdempotentStatement.{u} := by
  intro B _ G hG hAS T θ hidem hn
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let P := RestrictedAffinePoints.projectionData T G θ hG hAS hidem hn
  refine ⟨P.element, ⟨P.idempotent, P.formula⟩, ?_⟩
  intro e he
  apply IdempotentProjection.eq_of_proj_eq G
    (IdempotentProjection.isFibrewiseNontrivial_of_isAlmostSimple G hAS) he.1 P.idempotent
  intro X x
  have hP := (IdempotentPoints.eq_proj_iff G (P.idempotent.map X.hom.hom)).mpr (P.formula X x)
  have he' := (IdempotentPoints.eq_proj_iff G (he.1.map X.hom.hom)).mpr (he.2 X x)
  exact he'.symm.trans hP

end Langlands.GroupScheme
