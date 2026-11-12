import Langlands.GroupScheme.Rational.RelativeRootAbsoluteRestrictionStatement
import Langlands.GroupScheme.Rational.AbsoluteRootRestriction

/-! # Relative roots as restrictions of absolute roots: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false in
/-- The relative roots of a maximal split torus are the nonzero characters whose base change
is the restriction of a root for a containing maximal torus split over the extension field
(Milne, *Algebraic Groups* (2017), 25.19). -/
theorem relativeRootAbsoluteRestriction : RelativeRootAbsoluteRestrictionStatement.{u} := by
  intro k K _ _ _ G hG S i hi T j f _hj hf hTK
  have := hG.isAffineHom
  have := hG.smooth
  intro α
  subst hf
  exact mem_roots_iff_exists_splittingField_restriction hi.1.1 hTK f j α

end Langlands.GroupScheme
