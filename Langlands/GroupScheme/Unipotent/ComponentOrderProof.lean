import Langlands.GroupScheme.Unipotent.ComponentOrderStatement
import Langlands.GroupScheme.ComponentPointQuotient
import Langlands.GroupScheme.Rational.UnipotentPointsPGroup
import Langlands.GroupScheme.Unipotent.CharZeroConnectedProof

/-! # The order of the geometric component group of a unipotent group -/

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits (pullback)
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open GaloisPointComparison IdentityComponent

/-- The number of geometric components of a unipotent affine algebraic group
is a power of the characteristic exponent. -/
theorem unipotentComponentOrder : UnipotentComponentOrderStatement.{u} := by
  intro k _ p hChar G _ _ hG
  let H := baseChanged k (AlgebraicClosure k) G
  let : IsAffineHom H.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (baseMap k (AlgebraicClosure k))))
  let : LocallyOfFiniteType H.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom (baseMap k (AlgebraicClosure k))))
  have hH : IsUnipotent H := hG.baseChange
  rcases hChar with _ | ⟨hp⟩
  · let : ConnectedSpace H.X.left :=
      Unipotent.connectedSpace_of_isUnipotent_of_isAlgClosed H hH
    refine ⟨0, ?_⟩
    change Nat.card (_root_.ConnectedComponents H.X.left) = (1 : ℕ) ^ 0
    rw [pow_zero]
    exact Nat.card_unique
  · let : Fact p.Prime := ⟨hp⟩
    let : CharP (AlgebraicClosure k) p :=
      charP_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective p
    have hPoints : IsPGroup p (rationalPoints H) :=
      isPGroup_testPoints_of_isUnipotent p hH _
    rw [natCard_geometricComponents_eq_componentPointQuotient G]
    exact IsPGroup.iff_card.mp (hPoints.of_surjective (componentPointProjection H)
      (componentPointProjection_surjective H))

end Langlands.GroupScheme
