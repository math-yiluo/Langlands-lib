import Langlands.HarmonicAnalysis.Distribution.RenardEssentialProductsStatements
import Langlands.Algebra.IdempotentedRingRightLimitRing

/-! # Renard II.3.13: the actual completed Hecke algebra -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.Distribution.RenardCompletion

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- The exact comparison with the published compatible-family carrier and its
published ring product; coordinates run over all Hecke idempotents. -/
def ComparisonSpecification
    (hA : Langlands.Algebra.IsIdempotented (Hecke.HeckeAlgebra μ))
    (p : rightEssentiallyCompact μ →ₗ[ℂ]
      rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ)
    (E : rightEssentiallyCompact μ ≃+
      Langlands.Algebra.IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ)) : Prop :=
  (∀ (T : rightEssentiallyCompact μ)
      (e : Langlands.Algebra.Idempotent (Hecke.HeckeAlgebra μ)),
    heckeDistribution μ ((E T).val e) =
      rightHeckeConvolution μ (T : Distribution G) (e : Hecke.HeckeAlgebra μ)) ∧
  (∀ (c : ℂ) (T : rightEssentiallyCompact μ)
      (e : Langlands.Algebra.Idempotent (Hecke.HeckeAlgebra μ)),
    (E (c • T)).val e = c • (E T).val e) ∧
  (∀ T U : rightEssentiallyCompact μ,
    E (p T U) =
      Langlands.Algebra.IdempotentedRingRightLimit.product hA (E T) (E U)) ∧
  (∃ d : rightEssentiallyCompact μ, (d : Distribution G) = dirac 1 ∧
    E d = Langlands.Algebra.IdempotentedRingRightLimit.unit) ∧
  (∀ h : Hecke.HeckeAlgebra μ,
    ∃ H : rightEssentiallyCompact μ, (H : Distribution G) = heckeDistribution μ h ∧
      E H = Langlands.Algebra.IdempotentedRingRightLimit.canonical h) ∧
  ∀ (a : Langlands.Algebra.IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ))
    (f : SchwartzBruhat G) (e : Langlands.Algebra.Idempotent (Hecke.HeckeAlgebra μ)),
    rightConvolveTest f (heckeDistribution μ (e : Hecke.HeckeAlgebra μ)) = (f : G → ℂ) →
    GroupAction.inversionDistributions (heckeDistribution μ (e : Hecke.HeckeAlgebra μ)) =
        heckeDistribution μ (e : Hecke.HeckeAlgebra μ) →
    (E.symm a : Distribution G) f = heckeDistribution μ (a.val e) f

/-- II.3.13 Theorem: existence of the source product and of the uniquely
specified complex-algebra comparison with the actual idempotented completion. -/
def Statements : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure],
    ∃ hA : Langlands.Algebra.IsIdempotented (Hecke.HeckeAlgebra μ),
      ∃ p : rightEssentiallyCompact μ →ₗ[ℂ]
          rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ,
        RenardEssentialProducts.RightProductSpecification μ p ∧
        ∃! E : rightEssentiallyCompact μ ≃+
            Langlands.Algebra.IdempotentedRingRightLimit (Hecke.HeckeAlgebra μ),
          ComparisonSpecification μ hA p E

end Langlands.HarmonicAnalysis.Distribution.RenardCompletion
