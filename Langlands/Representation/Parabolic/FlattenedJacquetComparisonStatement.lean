import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Parabolic.ComposedFunctors

/-! The actual composed and standard flattened upper Jacquet quotients. -/

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uK uF uV

/-- The composed upper radical is the standard upper radical of the actual
ordered flattened shape, with no conjugation or coordinate change. -/
def FlattenedUnipotentComparisonStatement : Prop :=
  ∀ (K : Type uK) [CommRing K] (n : ℕ) (B : BlockShape n)
    (S : BlockRefinement B),
    composedUnipotent K B S = (B.flatten S).unipotentSubgroup K

/-- The normalized composed quotient, pulled back to the flattened product
Levi, is equivariantly equivalent to the standard normalized upper Jacquet
quotient. The equivalence sends the class of every original vector to its
class. -/
def FlattenedNormalizedJacquetComparisonStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
    ∃ φ : Representation.Equiv
      ((T.normalizedComposedJacquet B S ρ).comp
        (flattenedLeviEquiv F.Carrier B S).toMonoidHom)
      (T.normalizedJacquet (B.flatten S) ρ),
      ∀ v : V, φ (composedJacquetMk B S ρ v) = (B.flatten S).jacquetMk ρ v

/-- The subgroup identity and normalized representation comparison, with
independent ring, field and representation-carrier universes. -/
def FlattenedJacquetComparisonStatement : Prop :=
  FlattenedUnipotentComparisonStatement.{uK} ∧
    FlattenedNormalizedJacquetComparisonStatement.{uF, uV}

end Langlands.Parabolic
