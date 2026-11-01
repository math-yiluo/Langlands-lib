import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Exponents.Chambers
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Jacquet.Parabolic

/-! # Strict cones for actual scalar Jacquet subquotients -/

namespace Langlands

universe uF uV

/-- Every real part of the scalar character of a nonzero actual normalized
upper Jacquet subquotient of an analytically square-integrable representation
has zero total and strictly positive proper prefix sums. -/
def SquareIntegrableActualJacquetConeStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n →
      ∀ (π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)),
        T.IsSquareIntegrable π.representation →
        ∀ (B : GeneralLinear.BlockShape n)
          (S : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)) [Nontrivial S],
          SmoothRep.IsSubquotient S ((T.normalizedJacquetFunctor B).obj π) →
          ∀ (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
            (∀ (a : Fin B.length → F.Carrierˣ) (v : S),
              S.representation (B.blockScalarLevi F.Carrier a) v = (χ a : ℂ) • v) →
            ∀ (x : Fin B.length → ℝ), T.IsRealPartOf χ x →
              Exponents.IsPositiveRootCone x

end Langlands
