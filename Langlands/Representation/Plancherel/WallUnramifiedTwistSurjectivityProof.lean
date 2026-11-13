import Langlands.Representation.Plancherel.WallUnramifiedTwistSurjectivityStatement
import Langlands.Representation.Plancherel.RationalJointRestriction
import Langlands.GroupScheme.Rational.WallCharacterSum

/-! # Proof of unramified-twist surjectivity across a rank-one wall -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

/-- Unramified twists across a rank-one wall: every unramified character of the common
Levi `L(k)` is the product of the restrictions of an unramified character of `M(k)` and
one of `M₁(k)`. -/
theorem wallUnramifiedTwistSurjectivity : WallUnramifiedTwistSurjectivityStatement.{u} := by
  intro k _ _ _ _ G hG P M Q L P₁ M₁ Q₁ p m q l p₁ m₁ q₁ l₁ hp hm hq hl hp₁ hm₁ hq₁ hl₁
    hcomm hne hmax A a b ha hb hnc φ
  have := hm.isConnectedReductive.smooth
  have := hm₁.isConnectedReductive.smooth
  have : IsAffine M.X.left :=
    haveI := hm.isConnectedReductive.isAffineHom; isAffine_of_isAffineHom M.X.hom
  have : IsAffine L.X.left :=
    haveI := hl.isConnectedReductive.isAffineHom; isAffine_of_isAffineHom L.X.hom
  have : IsAffine M₁.X.left :=
    haveI := hm₁.isConnectedReductive.isAffineHom; isAffine_of_isAffineHom M₁.X.hom
  obtain ⟨⟨ψ, χ⟩, h⟩ := rationalUnramifiedCharacterProductRestrict_surjective_of_nsmul
    (l ≫ q) (l₁ ≫ q₁)
    (GroupScheme.WallCharacterSum.exists_nsmul_eq_restrict_add hG hp hm hq hl hp₁ hm₁ hq₁ hl₁
      hcomm hne hmax ha hb hnc) φ
  exact ⟨ψ, χ, h.symm⟩

end Langlands.Plancherel
