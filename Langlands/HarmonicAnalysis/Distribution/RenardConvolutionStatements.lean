import Langlands.HarmonicAnalysis.Distribution.Convolution
import Langlands.HarmonicAnalysis.Distribution.Haar
import Langlands.Representation.Hecke.Convolution

/-! # Renard II.3.10: laws of distribution convolution -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.Distribution.RenardConvolution

universe uG

/-- Agreement with the source's ambient tensor and extended pairing formula. -/
def AmbientTensorStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (T S : compactlySupported (X := G)),
    ∃ h : IsCompact (support (tensor (T : Distribution G) (S : Distribution G))),
      ∀ f : SchwartzBruhat G, (convolution T S : Distribution G) f =
        compactSupportPairing ⟨tensor (T : Distribution G) (S : Distribution G), h⟩
          ⟨fun p : G × G => f (p.1 * p.2),
            f.locallyConstant.comp_continuous (continuous_fst.mul continuous_snd)⟩

/-- All four scalar kernels are locally constant; compact inputs preserve tests
and the test and smooth definitions agree. -/
def RegularityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G],
    (∀ (D : Distribution G) (f : SchwartzBruhat G),
      IsLocallyConstant (leftConvolveTest D f) ∧
        IsLocallyConstant (rightConvolveTest f D)) ∧
    (∀ (T : compactlySupported (X := G)) (f : LocallyConstant G ℂ),
      IsLocallyConstant (leftConvolveSmooth T f) ∧
        IsLocallyConstant (rightConvolveSmooth f T)) ∧
    ∀ (T : compactlySupported (X := G)) (f : SchwartzBruhat G),
      HasCompactSupport (leftConvolveTest (T : Distribution G) f) ∧
      HasCompactSupport (rightConvolveTest f (T : Distribution G)) ∧
      leftConvolveSmooth T ⟨(f : G → ℂ), f.locallyConstant⟩ =
        leftConvolveTest (T : Distribution G) f ∧
      rightConvolveSmooth ⟨(f : G → ℂ), f.locallyConstant⟩ T =
        rightConvolveTest f (T : Distribution G)

/-- Proposition (ii), on the original compact-support carrier and operation. -/
def AssociativityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (T S R : compactlySupported (X := G)),
    convolution (convolution T S) R = convolution T (convolution S R)

/-- Proposition (iii), with pointwise specified locally constant intermediate
functions, so every operation has its original published domain. -/
def MixedAssociativityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (T S : compactlySupported (X := G)) (f : SchwartzBruhat G),
    ∃ lT rT lS rS : LocallyConstant G ℂ,
      (lT : G → ℂ) = leftConvolveTest (T : Distribution G) f ∧
      (rT : G → ℂ) = rightConvolveTest f (T : Distribution G) ∧
      (lS : G → ℂ) = leftConvolveTest (S : Distribution G) f ∧
      (rS : G → ℂ) = rightConvolveTest f (S : Distribution G) ∧
      leftConvolveTest (convolution T S : Distribution G) f =
        leftConvolveSmooth T lS ∧
      leftConvolveSmooth T rS = rightConvolveSmooth lT S ∧
      rightConvolveSmooth rT S =
        rightConvolveTest f (convolution T S : Distribution G)

/-- Proposition (iv), for the actual left and right invariant measure densities.
Finite-on-compacts right invariant measures suffice for the right-hand identity. -/
def HaarDensityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ ν : Measure G) [μ.IsHaarMeasure]
    [IsFiniteMeasureOnCompacts ν] [ν.IsMulRightInvariant]
    (T : compactlySupported (X := G)) (f : SchwartzBruhat G),
    ∃ Fμ Fν : compactlySupported (X := G),
      (Fμ : Distribution G) = testDensity μ f ∧
      (Fν : Distribution G) = testDensity ν f ∧
      ∃ l r : SchwartzBruhat G,
        (l : G → ℂ) = leftConvolveTest (T : Distribution G) f ∧
        (r : G → ℂ) = rightConvolveTest f (T : Distribution G) ∧
        (convolution T Fμ : Distribution G) = testDensity μ l ∧
        (convolution Fν T : Distribution G) = testDensity ν r

/-- Proposition (v), for every algebraic distribution. -/
def EvaluationStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (D : Distribution G) (f : SchwartzBruhat G),
    D f = leftConvolveTest D (Hecke.TestFunction.inversion f) 1 ∧
      D f = rightConvolveTest (Hecke.TestFunction.inversion f) D 1

/-- Bilinearity and the actual Dirac identity element. -/
def BilinearUnitStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G],
    (∀ (T S R : compactlySupported (X := G)),
      convolution (T + S) R = convolution T R + convolution S R) ∧
    (∀ (T S R : compactlySupported (X := G)),
      convolution T (S + R) = convolution T S + convolution T R) ∧
    (∀ (c : ℂ) (T S : compactlySupported (X := G)),
      convolution (c • T) S = c • convolution T S) ∧
    (∀ (c : ℂ) (T S : compactlySupported (X := G)),
      convolution T (c • S) = c • convolution T S) ∧
    ∀ T : compactlySupported (X := G),
      convolution (compactDirac 1) T = T ∧ convolution T (compactDirac 1) = T

/-- The three formulas in the II.3.10 Lemma. -/
def DiracStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (T : compactlySupported (X := G)) (g g' : G),
    (convolution (compactDirac g) T : Distribution G) =
      GroupAction.leftDistributions g (T : Distribution G) ∧
    (convolution T (compactDirac g) : Distribution G) =
      GroupAction.rightDistributions g⁻¹ (T : Distribution G) ∧
    convolution (compactDirac g) (compactDirac g') = compactDirac (g * g')

/-- The concrete bridge to the already published left-Haar Hecke product. -/
def HeckeCompatibilityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (f g : SchwartzBruhat G),
    ∃ F H : compactlySupported (X := G),
      (F : Distribution G) = testDensity μ f ∧
      (H : Distribution G) = testDensity μ g ∧
      (convolution F H : Distribution G) =
        testDensity μ (Hecke.TestFunction.convolution μ f g)

def Statements : Prop :=
  AmbientTensorStatement.{uG} ∧ RegularityStatement.{uG} ∧
    AssociativityStatement.{uG} ∧ MixedAssociativityStatement.{uG} ∧
    HaarDensityStatement.{uG} ∧ EvaluationStatement.{uG} ∧
    BilinearUnitStatement.{uG} ∧ DiracStatement.{uG} ∧
    HeckeCompatibilityStatement.{uG}

end Langlands.HarmonicAnalysis.Distribution.RenardConvolution
