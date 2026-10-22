import Langlands.Geometry.Analytic.RationalIntersection.Definitions

/-! # Target for intersections of actual rational localization spectra -/

universe u

namespace Langlands.Analytic.RationalIntersection

/-- The product quotient realizes the intersection and receives bounded
restriction maps from the two original rational localization algebras. -/
def IntersectionStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K) (m n : ℕ)
    (g h : P) (f : Fin m → P) (k : Fin n → P),
    RationalLocalization.GeneratesUnitIdeal K P m g f →
    RationalLocalization.GeneratesUnitIdeal K P n h k →
    RationalLocalization.GeneratesUnitIdeal K P ((m + 1) * (n + 1))
      (g * h) (numerators K P m n g h f k) ∧
    RationalLocalization.locus K P ((m + 1) * (n + 1))
        (g * h) (numerators K P m n g h f k) =
      RationalLocalization.locus K P m g f ∩ RationalLocalization.locus K P n h k ∧
    Set.range (BanachSpectrum.comap (baseMap K P m n g h f k).toBoundedRingHom) =
      RationalLocalization.locus K P m g f ∩ RationalLocalization.locus K P n h k ∧
    Topology.IsClosedEmbedding
      (BanachSpectrum.comap (baseMap K P m n g h f k).toBoundedRingHom) ∧
    ∃ L : BoundedAlgHom K (RationalLocalization.algebra K P m g f)
        (algebra K P m n g h f k),
    ∃ R : BoundedAlgHom K (RationalLocalization.algebra K P n h k)
        (algebra K P m n g h f k),
      L.comp (RationalLocalization.baseMap K P m g f) = baseMap K P m n g h f k ∧
      R.comp (RationalLocalization.baseMap K P n h k) = baseMap K P m n g h f k

end Langlands.Analytic.RationalIntersection
