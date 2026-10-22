import Langlands.Geometry.Analytic.StrictTestDomain.RationalRepresentationStatement
import Langlands.Geometry.Analytic.RationalFactorization

/-! # Rational representation with presented strict affinoid tests: proof -/

universe u

namespace Langlands.Analytic.StrictTestDomain

/-- The constructed rational quotient represents its closed rational locus for
all presented strict affinoid tests, from the absence of common spectrum zeros. -/
theorem rationalRepresentation : RationalRepresentationStatement.{u} := by
  intro K _ _ _ P d
  have hunit : RationalLocalization.GeneratesUnitIdeal K P d.arity d.denominator
      d.numerator :=
    (RationalFactorization.generatesUnitIdeal_iff_no_common_zero K P d.arity
      d.denominator d.numerator).mpr d.no_common_zero
  have hrange : Set.range (BanachSpectrum.comap d.baseMap.toBoundedRingHom) = d.locus :=
    RationalLocalization.range_comap_baseMap K P d.arity d.denominator d.numerator hunit
  refine ⟨?_, hrange, ?_⟩
  · rw [← hrange]
    exact (RationalLocalization.comap_baseMap_closedEmbedding K P d.arity d.denominator
      d.numerator hunit).isClosed_range
  · intro R φ hφ
    exact (RationalFactorization.factorization_of_no_common_zero K P d.arity d.denominator
      d.numerator R φ d.no_common_zero).mp hφ

end Langlands.Analytic.StrictTestDomain
