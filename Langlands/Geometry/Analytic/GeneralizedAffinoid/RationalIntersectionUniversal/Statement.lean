import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalIntersection

/-! # Bounded pushout target for positive-polyradius rational intersections -/

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.RationalIntersection

open GeneralizedTateAlgebra

/-- The actual all-products quotient, with its constructed restrictions from the
two original weighted rational quotients, is their bounded pushout over the
coefficient algebra for complete ultrametric normed commutative targets. -/
def BoundedPushoutStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : PresentedAffinoidAlgebra K) (m n : ℕ)
    (s : PositivePolyradius (Fin m)) (t : PositivePolyradius (Fin n))
    (g h : GeneralizedTateAlgebra A.polyradius K)
    (f : Fin m → GeneralizedTateAlgebra A.polyradius K)
    (k : Fin n → GeneralizedTateAlgebra A.polyradius K)
    (hf : GeneratesUnitIdeal K A g f) (hk : GeneratesUnitIdeal K A h k),
    (leftMap K A s t g h f k hf hk).comp (baseMap K A s g f) = base K A s t g h f k ∧
    (rightMap K A s t g h f k hf hk).comp (baseMap K A t h k) = base K A s t g h f k ∧
    ∀ (E : Type v) [NormedCommRing E] [NormedAlgebra K E]
      [IsUltrametricDist E] [CompleteSpace E]
      (α : BoundedAlgHom K (algebra K A s g f) E)
      (β : BoundedAlgHom K (algebra K A t h k) E),
      α.comp (baseMap K A s g f) = β.comp (baseMap K A t h k) →
      ∃! θ : BoundedAlgHom K (Algebra K A s t g h f k) E,
        θ.comp (leftMap K A s t g h f k hf hk) = α ∧
          θ.comp (rightMap K A s t g h f k hf hk) = β

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation.RationalIntersection
