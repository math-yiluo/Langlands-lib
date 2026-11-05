import Langlands.GroupScheme.Rational.PositivePowerFactorizationData
import Langlands.GroupScheme.Rational.CharacteristicZeroPointFactors

/-! # Positive-power torus and additive factorization of rational points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every rational point of an affine locally finite type field group has
actual commuting torus and additive factors after a positive power. -/
theorem nonempty_factorizationData
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (x : rationalPoints G) :
    Nonempty (TorusAdditivePowerFactorizationData G x) := by
  rcases CharP.exists' k with hchar | ⟨p, hp, hchar⟩
  · let : CharZero k := hchar
    let E := connectedCommutativePowerEnvelope G x
    let : Smooth E.group.toGrp.X.hom := E.smooth
    let : IsAffineHom E.group.toGrp.X.hom := E.affine
    let : ConnectedSpace E.group.toGrp.X.left := E.connected
    obtain ⟨T, i, t, φ, hT, hi, heq⟩ :=
      characteristicZeroPointFactors k E.group E.point
    exact ⟨E.factorizationOfPointFactors T i t φ hT hi heq⟩
  · let : Fact p.Prime := hp
    let : CharP k p := hchar
    exact ⟨positiveCharacteristicFactorizationData G x p⟩

/-- Choose actual commuting torus and additive factors for a positive power. -/
def positivePowerFactorizationData
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (x : rationalPoints G) :
    TorusAdditivePowerFactorizationData G x :=
  Classical.choice (nonempty_factorizationData G x)

/-- A positive power is a product of the actual torus and additive point
images, and these two chosen factors commute in the ambient point group. -/
theorem positivePowerTorusAdditiveFactorization_commute
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (x : rationalPoints G) :
    ∃ (m : ℕ), 0 < m ∧
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
        (t : rationalPoints T.toGrp)
        (φ : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G),
        IsTorus T.toGrp ∧ IsClosedSubgroup i ∧
          x ^ m = rationalPoints.map i t *
            rationalPoints.map φ (VectorGroup.coordinateOnePoint k) ∧
          Commute (rationalPoints.map i t)
            (rationalPoints.map φ (VectorGroup.coordinateOnePoint k)) := by
  let D := positivePowerFactorizationData G x
  exact ⟨D.exponent, D.exponent_pos, D.torus, D.inclusion, D.point, D.additive,
    D.isTorus, D.closed, D.factorization, D.commute⟩

/-- Forgetting the commuting-factor field gives the exact Library target. -/
theorem positivePowerTorusAdditiveFactorization :
    PositivePowerTorusAdditiveFactorizationStatement.{u} := by
  intro k _ G _ _ x
  obtain ⟨m, hm, T, i, t, φ, hT, hi, heq, _⟩ :=
    positivePowerTorusAdditiveFactorization_commute k G x
  exact ⟨m, hm, T, i, t, φ, hT, hi, heq⟩

end Langlands.GroupScheme
