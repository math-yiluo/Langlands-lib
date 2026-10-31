import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalRepresentationStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalExtension
import Langlands.Geometry.Analytic.GeneralizedAffinoid.SpectralPowerBoundProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.SpectrumIdealCriterionProof

/-! # Rational representation against arbitrary positive-radius affinoid tests: proof -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open GeneralizedTateAlgebra

namespace RationalChart

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

omit [CompleteSpace K] in
/-- The structural spectrum map has exactly the chart locus as its range. -/
theorem range_comap_baseMap (d : RationalChart K A) :
    Set.range (BanachSpectrum.comap d.baseMap.toBoundedRingHom) = d.locus :=
  RationalPresentation.range_spectrumMap K A d.radii d.denominator d.numerators d.generates

/-- A test map whose spectrum image lies in the locus sends the denominator to a
unit: no spectrum point of the test algebra vanishes on its image. -/
theorem isUnit_denominator_of_hasImageIn (d : RationalChart K A)
    {R : PresentedAffinoidAlgebra K} (φ : BoundedAlgHom K A R)
    (hφ : HasImageIn K φ d.locus) :
    IsUnit (φ (presentationMap K A d.denominator)) := by
  apply ((spectrumIdealCriterion K).2.1 R _).mpr
  intro y
  exact RationalPresentation.denominator_ne_zero K A d.radii d.denominator d.numerators
    d.generates _ (hφ y)

omit [CompleteSpace K] in
/-- The fractions obtained from the inverse of the denominator image are
spectrally bounded by the chart radii. -/
theorem spectrum_fraction_le (d : RationalChart K A)
    {R : PresentedAffinoidAlgebra K} (φ : BoundedAlgHom K A R)
    (hφ : HasImageIn K φ d.locus) (u : Rˣ)
    (hu : (u : R) = φ (presentationMap K A d.denominator)) (j : Fin d.arity)
    (y : BanachSpectrum R) :
    y (↑u⁻¹ * φ (presentationMap K A (d.numerators j))) ≤ d.radii j := by
  have hloc : y (φ (presentationMap K A (d.numerators j))) ≤
      d.radii j * y (φ (presentationMap K A d.denominator)) := hφ y j
  have hone : y (↑u⁻¹ : R) * y (u : R) = 1 := by
    rw [← map_mul y.toMulRingSeminorm, Units.inv_mul, map_one]
  rw [← hu] at hloc
  calc
    y (↑u⁻¹ * φ (presentationMap K A (d.numerators j))) =
        y (↑u⁻¹ : R) * y (φ (presentationMap K A (d.numerators j))) :=
      map_mul y.toMulRingSeminorm _ _
    _ ≤ y (↑u⁻¹ : R) * (d.radii j * y (u : R)) :=
      mul_le_mul_of_nonneg_left hloc (apply_nonneg y.toMulRingSeminorm _)
    _ = d.radii j * (y (↑u⁻¹ : R) * y (u : R)) := by ring
    _ = d.radii j := by rw [hone, mul_one]

/-- Every bounded test map with spectrum image in the locus factors uniquely
through the structural map of the chart. -/
theorem existsUnique_factorization (d : RationalChart K A)
    (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K A R)
    (hφ : HasImageIn K φ d.locus) :
    ∃! ψ : BoundedAlgHom K d.algebra R, ψ.comp d.baseMap = φ := by
  let u : Rˣ := (isUnit_denominator_of_hasImageIn d φ hφ).unit
  have hu : (u : R) = φ (presentationMap K A d.denominator) :=
    (isUnit_denominator_of_hasImageIn d φ hφ).unit_spec
  let b : Fin d.arity → R := fun j => ↑u⁻¹ * φ (presentationMap K A (d.numerators j))
  have hb : HasBoundedMonomials d.radii R b :=
    (hasBoundedMonomials_iff_radiusBoundedPowers d.radii R b).mpr fun j =>
      spectralPowerBound (K := K) R (b j) (d.radii j) (d.radii.positive j)
        (spectrum_fraction_le d φ hφ u hu j)
  have heq : ∀ j, φ (presentationMap K A d.denominator) * b j =
      φ (presentationMap K A (d.numerators j)) := by
    intro j
    rw [← hu]
    exact Units.mul_inv_cancel_left u _
  exact RationalPresentation.existsUnique_extension K A d.radii d.denominator d.numerators
    R d.generates φ b hb heq

/-- Every actual rational chart represents its closed inequality locus against
all finite positive-polyradius affinoid tests. -/
theorem represents (d : RationalChart K A) : Represents K d.baseMap d.locus := by
  refine ⟨RationalPresentation.isClosed_locus K A d.radii d.denominator d.numerators,
    range_comap_baseMap d, ?_⟩
  intro R φ hφ
  exact existsUnique_factorization d R φ hφ

end RationalChart

/-- The unchanged rational representation statement, for every complete
ultrametric coefficient field, base quotient presentation and rational chart. -/
theorem rationalRepresentation : RationalRepresentationStatement.{u} := by
  intro K _ _ _ A d
  exact d.represents

end Langlands.Analytic.PresentedAffinoidAlgebra
