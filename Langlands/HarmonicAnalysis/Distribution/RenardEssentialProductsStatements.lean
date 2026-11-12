import Langlands.HarmonicAnalysis.Distribution.CompactSubgroup
import Langlands.HarmonicAnalysis.Distribution.Convolution
import Langlands.HarmonicAnalysis.Distribution.HeckeRealization
import Langlands.Representation.Hecke.NormalizedIndicator

/-! # Renard II.3.13: products on the actual essentially compact submodules -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.Distribution.RenardEssentialProducts

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- Algebra laws for a bilinear product on an existing distribution submodule,
including extension of compact convolution and both full Hecke actions. -/
def AlgebraLaws (S : Submodule ℂ (Distribution G)) (p : S →ₗ[ℂ] S →ₗ[ℂ] S) : Prop :=
  (∀ T U V : S, p (p T U) V = p T (p U V)) ∧
  (∃ d : S, (d : Distribution G) = dirac 1 ∧
    ∀ T : S, p d T = T ∧ p T d = T) ∧
  (∀ T U : compactlySupported (X := G),
    ∃ t u : S, (t : Distribution G) = (T : Distribution G) ∧
      (u : Distribution G) = (U : Distribution G) ∧
      (p t u : Distribution G) = (convolution T U : Distribution G)) ∧
  ∀ (T : S) (h : Hecke.HeckeAlgebra μ),
    ∃ H : S, (H : Distribution G) = heckeDistribution μ h ∧
      (p T H : Distribution G) = rightHeckeConvolution μ (T : Distribution G) h ∧
      (p H T : Distribution G) = leftHeckeConvolution μ h (T : Distribution G)

/-- The right product is characterized by the source's evaluation formula
for every compact-open local idempotent fixing the scalar test on the right. -/
def RightProductSpecification
    (p : rightEssentiallyCompact μ →ₗ[ℂ]
      rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ) : Prop :=
  AlgebraLaws μ (rightEssentiallyCompact μ) p ∧
  (∀ (T U : rightEssentiallyCompact μ) (f : SchwartzBruhat G)
      (K : OpenSubgroup G) (hK : IsCompact (K : Set G)),
    rightConvolveTest f (compactSubgroupHaar K.toSubgroup hK : Distribution G) =
        (f : G → ℂ) →
    ∃ h : Hecke.HeckeAlgebra μ,
      heckeDistribution μ h = rightHeckeConvolution μ (U : Distribution G)
        (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) ∧
      (p T U : Distribution G) f = rightHeckeConvolution μ (T : Distribution G) h f) ∧
  ∀ (T U : rightEssentiallyCompact μ) (h : Hecke.HeckeAlgebra μ),
    ∃ k : Hecke.HeckeAlgebra μ,
      heckeDistribution μ k = rightHeckeConvolution μ (U : Distribution G) h ∧
      rightHeckeConvolution μ (p T U : Distribution G) h =
        rightHeckeConvolution μ (T : Distribution G) k

/-- The left analogue uses a compact-open idempotent fixing the test on the
left and the corresponding left Hecke-action identity. -/
def LeftProductSpecification
    (p : leftEssentiallyCompact μ →ₗ[ℂ]
      leftEssentiallyCompact μ →ₗ[ℂ] leftEssentiallyCompact μ) : Prop :=
  AlgebraLaws μ (leftEssentiallyCompact μ) p ∧
  (∀ (T U : leftEssentiallyCompact μ) (f : SchwartzBruhat G)
      (K : OpenSubgroup G) (hK : IsCompact (K : Set G)),
    leftConvolveTest (compactSubgroupHaar K.toSubgroup hK : Distribution G) f =
        (f : G → ℂ) →
    ∃ h : Hecke.HeckeAlgebra μ,
      heckeDistribution μ h = leftHeckeConvolution μ
        (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) (T : Distribution G) ∧
      (p T U : Distribution G) f = leftHeckeConvolution μ h (U : Distribution G) f) ∧
  ∀ (T U : leftEssentiallyCompact μ) (h : Hecke.HeckeAlgebra μ),
    ∃ k : Hecke.HeckeAlgebra μ,
      heckeDistribution μ k = leftHeckeConvolution μ h (T : Distribution G) ∧
      leftHeckeConvolution μ h (p T U : Distribution G) =
        leftHeckeConvolution μ k (U : Distribution G)

/-- On the actual intersection, the right and left products agree and retain
all the algebra laws. Every lift is constrained by its original distribution. -/
def TwoSidedProductSpecification
    (pr : rightEssentiallyCompact μ →ₗ[ℂ]
      rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ)
    (pl : leftEssentiallyCompact μ →ₗ[ℂ]
      leftEssentiallyCompact μ →ₗ[ℂ] leftEssentiallyCompact μ)
    (p : essentiallyCompact μ →ₗ[ℂ]
      essentiallyCompact μ →ₗ[ℂ] essentiallyCompact μ) : Prop :=
  AlgebraLaws μ (essentiallyCompact μ) p ∧
  ∀ T U : essentiallyCompact μ,
    ∃ (tr ur : rightEssentiallyCompact μ) (tl ul : leftEssentiallyCompact μ),
      (tr : Distribution G) = (T : Distribution G) ∧
      (ur : Distribution G) = (U : Distribution G) ∧
      (tl : Distribution G) = (T : Distribution G) ∧
      (ul : Distribution G) = (U : Distribution G) ∧
      (p T U : Distribution G) = (pr tr ur : Distribution G) ∧
      (p T U : Distribution G) = (pl tl ul : Distribution G)

/-- II.3.13 Lemma, including the choice-independent products specified in its
proof, on the three already published submodules of the original full dual. -/
def Statements : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure],
    (∃! p : rightEssentiallyCompact μ →ₗ[ℂ]
        rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ,
      RightProductSpecification μ p) ∧
    (∃! p : leftEssentiallyCompact μ →ₗ[ℂ]
        leftEssentiallyCompact μ →ₗ[ℂ] leftEssentiallyCompact μ,
      LeftProductSpecification μ p) ∧
    ∀ (pr : rightEssentiallyCompact μ →ₗ[ℂ]
        rightEssentiallyCompact μ →ₗ[ℂ] rightEssentiallyCompact μ)
      (pl : leftEssentiallyCompact μ →ₗ[ℂ]
        leftEssentiallyCompact μ →ₗ[ℂ] leftEssentiallyCompact μ),
      RightProductSpecification μ pr → LeftProductSpecification μ pl →
      ∃! p : essentiallyCompact μ →ₗ[ℂ]
          essentiallyCompact μ →ₗ[ℂ] essentiallyCompact μ,
        TwoSidedProductSpecification μ pr pl p

end Langlands.HarmonicAnalysis.Distribution.RenardEssentialProducts
