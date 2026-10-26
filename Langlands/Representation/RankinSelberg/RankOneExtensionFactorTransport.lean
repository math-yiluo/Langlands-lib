import Langlands.Representation.RankinSelberg.RankOneExtensionTransport
import Langlands.Representation.RankinSelberg.WhittakerTypeEquivalence

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (t : ℕ)
  (χ : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) (ULift.{uW} ℂ))
  (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
  (hχ : letI := F.canonicalTopologicalData.topology; IsSmooth χ)
  (hσ : letI := F.canonicalTopologicalData.topology; IsSmooth σ)

/-- Choose an actual intertwining equivalence to the exact upper induction.
This choice carries no prescribed formula on section evaluations. -/
def rankOneExtensionLowerToUpper :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (1 + (t + 1))
    Representation.Equiv (rankOneExtensionLowerInduced F t χ σ)
      (F.canonicalNormalizedProductInduced (rankOneExtensionUpperShape t)
        (Shahidi.pairFamily χ σ)) :=
  Classical.choice (rankOneExtensionLowerToUpperEquiv F t χ σ hχ hσ)

include hχ hσ

/-- The whole inverse-character Whittaker set is unchanged by reversal. -/
theorem rankOneExtensionInverseWhittakerSet_eq
    (ψ : letI := F.canonicalTopologicalData.topology;
      UnitaryAdditiveCharacter F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    inverseWhittakerSet ψ (1 + t) (rankOneExtensionLowerInduced F t χ σ) =
      inverseWhittakerSet ψ (1 + t)
        (F.canonicalNormalizedProductInduced (rankOneExtensionUpperShape t)
          (Shahidi.pairFamily χ σ)) := by
  let := F.canonicalTopologicalData.topology
  exact inverseWhittakerSet_eq_of_equiv ψ
    (rankOneExtensionLowerToUpper F t χ σ hχ hσ)

/-- All clauses of Whittaker type transport, without assuming irreducibility. -/
theorem rankOneExtensionWhittakerType_iff
    (ψ : letI := F.canonicalTopologicalData.topology;
      UnitaryAdditiveCharacter F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    IsOfWhittakerType (1 + t) (standardCharacter ψ (1 + t))
        (rankOneExtensionLowerInduced F t χ σ) ↔
      IsOfWhittakerType (1 + t) (standardCharacter ψ (1 + t))
        (F.canonicalNormalizedProductInduced (rankOneExtensionUpperShape t)
          (Shahidi.pairFamily χ σ)) := by
  let := F.canonicalTopologicalData.topology
  exact isOfWhittakerType_iff_of_equiv
    (rankOneExtensionLowerToUpper F t χ σ hχ hσ)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Certified polynomials for the actual pair transport with the same measure. -/
theorem rankOneExtensionSymmetricLPolynomial_iff
    (ψ : letI := F.canonicalTopologicalData.topology;
      UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier;
      AdditiveHaarMeasure F.Carrier)
    {r : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (P : ℂ[X]) :
    IsPadicSymmetricLPolynomial F ψ ν π (rankOneExtensionLowerInduced F t χ σ) P ↔
      IsPadicSymmetricLPolynomial F ψ ν π
        (F.canonicalNormalizedProductInduced (rankOneExtensionUpperShape t)
          (Shahidi.pairFamily χ σ)) P := by
  exact IsPadicSymmetricLPolynomial.congr_equiv (Representation.Equiv.refl π)
    (rankOneExtensionLowerToUpper F t χ σ hχ hσ)

/-- Every fixed rectangular zeta-value set transports without changing either measure. -/
theorem rankOneExtensionUnequalRankZetaValuesAt_eq
    (r j k : ℕ) (hr : r = (1 + t) + (j + k + 1))
    (q : ℕ)
    (ψ : letI := F.canonicalTopologicalData.topology;
      UnitaryAdditiveCharacter F.Carrier)
    (abv : AbsoluteValue F.Carrier ℝ)
    [MeasurableSpace (LeftUnipotentQuotient (1 + t) F.Carrier)]
    [MeasurableSpace (Matrix (Fin j) (Fin (1 + (t + 1))) F.Carrier)]
    (μ : Measure (LeftUnipotentQuotient (1 + t) F.Carrier))
    (η : Measure (Matrix (Fin j) (Fin (1 + (t + 1))) F.Carrier))
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V) :
    letI := F.canonicalTopologicalData.topology
    unequalRankZetaValuesAt j k hr q ψ abv μ η π (rankOneExtensionLowerInduced F t χ σ) =
      unequalRankZetaValuesAt j k hr q ψ abv μ η π
        (F.canonicalNormalizedProductInduced (rankOneExtensionUpperShape t)
          (Shahidi.pairFamily χ σ)) := by
  let := F.canonicalTopologicalData.topology
  exact unequalRankZetaValuesAt_eq_of_equiv j k q ψ abv μ η hr
    (Representation.Equiv.refl π) (rankOneExtensionLowerToUpper F t χ σ hχ hσ)

end Langlands.RankinSelberg
