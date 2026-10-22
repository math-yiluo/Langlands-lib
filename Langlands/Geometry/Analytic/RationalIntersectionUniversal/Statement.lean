import Langlands.Geometry.Analytic.RationalIntersection.Definitions

/-! # Target for the bounded pushout of rational localizations -/

universe u v

namespace Langlands.Analytic.RationalIntersection

/-- The actual product quotient receives bounded maps from both rational
localizations and is their pushout for complete ultrametric targets. -/
def BoundedPushoutStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K) (m n : ℕ)
    (g h : P) (f : Fin m → P) (k : Fin n → P),
    RationalLocalization.GeneratesUnitIdeal K P m g f →
    RationalLocalization.GeneratesUnitIdeal K P n h k →
    ∃ L : BoundedAlgHom K (RationalLocalization.algebra K P m g f)
        (algebra K P m n g h f k),
    ∃ R : BoundedAlgHom K (RationalLocalization.algebra K P n h k)
        (algebra K P m n g h f k),
      L.comp (RationalLocalization.baseMap K P m g f) = baseMap K P m n g h f k ∧
      R.comp (RationalLocalization.baseMap K P n h k) = baseMap K P m n g h f k ∧
      ∀ (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
        [IsUltrametricDist B] [CompleteSpace B]
        (α : BoundedAlgHom K (RationalLocalization.algebra K P m g f) B)
        (β : BoundedAlgHom K (RationalLocalization.algebra K P n h k) B),
        α.comp (RationalLocalization.baseMap K P m g f) =
          β.comp (RationalLocalization.baseMap K P n h k) →
        ∃! ψ : BoundedAlgHom K (algebra K P m n g h f k) B,
          ψ.comp L = α ∧ ψ.comp R = β

end Langlands.Analytic.RationalIntersection
