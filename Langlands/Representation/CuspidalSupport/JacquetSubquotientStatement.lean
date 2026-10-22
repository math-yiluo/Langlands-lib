import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Category.Subquotients

/-! Algebraic interfaces for carrying actual subquotients through Jacquet descent. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV uW

/-- The actual normalized Jacquet functor preserves actual subquotients. -/
def NormalizedJacquetSubquotientTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) (B : BlockShape n),
    letI := T.topology
    ∀ A D : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      SmoothRep.IsSubquotient D A →
      SmoothRep.IsSubquotient ((T.normalizedJacquetFunctor B).obj D)
        ((T.normalizedJacquetFunctor B).obj A)

/-- Equivalent ambient representations have equivalent actual normalized
Jacquet modules, even when their carriers lie in different universes. -/
def NormalizedJacquetEquivalenceTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) (B : BlockShape n),
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
      (D : SmoothRep.{0, uF, uW} ℂ (GeneralLinear n F.Carrier)),
      Nonempty (A.representation.Equiv D.representation) →
      Nonempty (((T.normalizedJacquetFunctor B).obj A).representation.Equiv
        ((T.normalizedJacquetFunctor B).obj D).representation)

/-- The two interfaces needed to descend a common actual subquotient. -/
def JacquetSubquotientTransportTheorem : Prop :=
  NormalizedJacquetSubquotientTheorem.{uF, uV} ∧
  NormalizedJacquetEquivalenceTheorem.{uF, uV, uW}

end Langlands.CuspidalSupport
