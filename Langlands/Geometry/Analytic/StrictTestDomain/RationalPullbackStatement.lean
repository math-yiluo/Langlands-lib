import Langlands.Geometry.Analytic.StrictTestDomain.RationalPullbackDefinitions

/-! # Rational inverse images and bounded base change -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain

/-- The actual pulled-back rational quotient represents the inverse-image
locus for strict tests and is a pushout among bounded maps to any complete
ultrametric normed K-algebra, including targets in another universe. -/
def RationalPullbackStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P Q : PresentedStrictAffinoidAlgebra K) (d : RationalData K P)
    (φ : BoundedAlgHom K P Q),
    Represents K (d.pullback φ).baseMap
      ((BanachSpectrum.comap φ.toBoundedRingHom) ⁻¹' d.locus) ∧
    ∃ i : BoundedAlgHom K d.algebra (d.pullback φ).algebra,
      i.comp d.baseMap = (d.pullback φ).baseMap.comp φ ∧
      (∀ i' : BoundedAlgHom K d.algebra (d.pullback φ).algebra,
        i'.comp d.baseMap = (d.pullback φ).baseMap.comp φ → i' = i) ∧
      ∀ (B : Type v) [NormedCommRing B] [IsUltrametricDist B]
        [NormedAlgebra K B] [CompleteSpace B]
        (a : BoundedAlgHom K d.algebra B) (b : BoundedAlgHom K Q B),
        a.comp d.baseMap = b.comp φ →
        ∃! c : BoundedAlgHom K (d.pullback φ).algebra B,
          c.comp i = a ∧ c.comp (d.pullback φ).baseMap = b

end Langlands.Analytic.StrictTestDomain
