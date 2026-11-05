import Langlands.Representation.Plancherel.CompactProductInducedCoefficients
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Spherical

/-! # Actual compact coefficients with spherical Haar normalization -/

noncomputable section

open MeasureTheory Langlands.Aubert.General
open scoped NNReal

namespace Langlands.Plancherel.CompactInduction

universe uG uV

section Measure

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  (K : OpenSubgroup G) [CompactSpace K] (hK : IsCompact (K : Set G))

local instance : IsTopologicalGroup K :=
  inferInstanceAs (IsTopologicalGroup (K : Subgroup G))

/-- The constructed compact-induction measure is exactly the Haar probability
used to define the spherical function. -/
theorem measure_eq_normalizedHaar :
    measure K hK = HarishChandraSchwartz.normalizedHaar (K : Subgroup G) :=
  Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

end Measure

section Integral

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G) [CompactSpace K]

/-- The actual diagonal contraction is integrable for spherical Haar probability,
by its local constancy on the compact subgroup. -/
theorem integrand_normalizedHaar_integrable
    (F : productInducedCoefficientObject h hU A) (g : G) :
    Integrable (integrand h hU A K g F) (HarishChandraSchwartz.normalizedHaar (K : Subgroup G)) :=
  (integrand_isLocallyConstant h hU A K F g).continuous
    |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Integrate the original product-induced diagonal contraction against the same
Haar probability as the spherical function. -/
def sphericalCoefficientIntegral :
    productInducedCoefficientObject h hU A →ₗ[ℂ] (G → ℂ) where
  toFun F g :=
    ∫ k : K, integrand h hU A K g F k ∂HarishChandraSchwartz.normalizedHaar (K : Subgroup G)
  map_add' F J := by
    funext g
    rw [map_add]
    exact integral_add (integrand_normalizedHaar_integrable h hU A K F g)
      (integrand_normalizedHaar_integrable h hU A K J g)
  map_smul' c F := by
    funext g
    change (∫ k : K, integrand h hU A K g (c • F) k
      ∂HarishChandraSchwartz.normalizedHaar (K : Subgroup G)) = _
    rw [map_smul]
    exact integral_smul c _

variable [SecondCountableTopology G] [T2Space G] [LocallyCompactSpace P]
  (hK : IsCompact (K : Set G))
  (hP : IsClosed (P : Set G)) (hm : Continuous h.projection)
  (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  (hA : A.IsAdmissible)

/-- The constructed coefficient map on the unchanged product-induced carrier
equals the spherical-Haar integral of its original diagonal contraction. -/
theorem coefficientMap_eq_sphericalCoefficientIntegral
    (F : productInducedCoefficientObject h hU A) (g : G) :
    coefficientMap h hU A K hK hP hm hPK hG hδ hA F g =
      sphericalCoefficientIntegral h hU A K F g := by
  change coefficientMap h hU A K hK hP hm hPK hG hδ hA F g =
    ∫ k : K, integrand h hU A K g F k ∂HarishChandraSchwartz.normalizedHaar (K : Subgroup G)
  rw [coefficientMap_integral, measure_eq_normalizedHaar K hK]

end Integral

end Langlands.Plancherel.CompactInduction
