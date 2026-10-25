import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Parabolic.OppositeRefinementFunctors
import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement

/-! The actual flattened and composed opposite Jacquet quotients. -/

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uK uF uV

/-- The composed opposite radical is the standard radical of the actual
ordered flattened shape, with no conjugation or coordinate change. -/
def FlattenedOppositeUnipotentComparisonStatement : Prop :=
  ∀ (K : Type uK) [CommRing K] (n : ℕ) (B : BlockShape n)
    (S : BlockRefinement B),
    composedOppositeUnipotent K B S =
      (B.flatten S).oppositeUnipotentSubgroup K

/-- The normalized composed quotient, pulled back to the flattened product
Levi, is equivariantly equivalent to its standard opposite quotient. The
equivalence sends the class of every original vector to its class. -/
def FlattenedNormalizedOppositeJacquetComparisonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B : BlockShape n) (S : BlockRefinement B)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)),
    ∃ φ : Representation.Equiv
      ((T.normalizedComposedOppositeJacquet B S A.ρ).comp
        (flattenedLeviEquiv F.Carrier B S).toMonoidHom)
      (CuspidalJacquetMultiplicity.oppositeJacquet T (B.flatten S) A).ρ,
      ∀ v : A,
        φ (composedOppositeJacquetMk B S A.ρ v) =
          Jacquet.mk A.ρ ((B.flatten S).oppositeUnipotentSubgroup F.Carrier) v

/-- The subgroup identity and normalized representation comparison, with
independent ring, field and representation-carrier universes. -/
def FlattenedOppositeJacquetComparisonStatement : Prop :=
  FlattenedOppositeUnipotentComparisonStatement.{uK} ∧
    FlattenedNormalizedOppositeJacquetComparisonStatement.{uF, uV}

end Langlands.Parabolic
