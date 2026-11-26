import Langlands.Global.AdelicEisensteinConvergenceProof
import Langlands.Global.AdelicNormalizedConvolutionHolomorphy
import Langlands.Global.AdelicSymmetricFamilyGram
import Langlands.Global.AdelicWavePacketConvolutionAssembly
import Langlands.Global.AdelicWavePacketConvolutionReduction
import Langlands.Global.RightTranslationTestFunctionSeparationProof

/-! # Analytic reduction of symmetric adelic wave-packet translation -/

noncomputable section

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Local function-valued meromorphic continuation yields joint continuity and the
convolution identity on the imaginary axis for the supplied scalar continuations. -/
theorem imaginaryEisensteinConvolution_of_meromorphicContinuation
    (hMero : EisensteinMeromorphicContinuationStatement.{0}) :
    ImaginaryEisensteinConvolutionStatement := by
  intro F _ _ G P M U A _ _ _ _ p _ iU l a r _ _ _ hA hT hG hUR K hK N d rho hsmooth hcalc
    hN hmax hrho Aut v hv E D hD hE hreg
  refine ⟨fun _ e => continuous_eisensteinContinuation_imaginary r hA hT hK hMero hG hUR
    rho hN hrho hsmooth hcalc hmax hv hE hreg hD e, ?_⟩
  intro kernel hk hks m u b E' D' hu hSpan hE' x g
  have hb (j : Fin m) : IsHolomorphicInCoordinatesOn (b j) univ :=
    ⟨(hSpan.1 j).1, fun n e => ((hSpan.1 j).2 n e).2.2.1⟩
  have hspan (lam : ComplexCharacterParameter F P) :
      hK.inducedConvolution lam kernel v = fun y => ∑ j, b j lam * u j y :=
    funext (hSpan.2 lam)
  exact rightConvolution_eisensteinContinuation_eq r hA hT hK hMero hG hUR rho hN hrho hsmooth
    hcalc hmax hv hE hreg hk hks hu hE'.2.1 hE'.2.2 hb hspan
    ⟨hD ⟨x, rfl⟩, hE'.1 ⟨x, rfl⟩⟩ g

/-- The finite imaginary convolution span, meromorphic continuation, holomorphy on the
imaginary axis, square-integrable intertwining expansions, and the wave-packet
inner-product theorem imply symmetric wave-packet translation approximation. -/
def WavePacketTranslationAnalyticReductionStatement : Prop :=
  NormalizedConvolutionImaginarySpanStatement →
  EisensteinMeromorphicContinuationStatement.{0} → EisensteinImaginaryAxisHolomorphyStatement →
  IntertwiningSquareIntegrableExpansionStatement → WavePacketInnerProductStatement →
  WavePacketTranslationStatement

theorem wavePacketTranslationAnalyticReduction : WavePacketTranslationAnalyticReductionStatement := by
  intro hSpan hMero hHolo hExp hWP
  exact wavePacketTranslation_of_analyticInputs rightTranslationTestFunctionSeparation
    (symmetricFamilyGramBridge hWP hExp inducedRestrictionMemLp)
    (normalizedConvolutionFiniteSpan_of_imaginarySpan hSpan)
    (imaginaryEisensteinConvolution_of_meromorphicContinuation hMero)
    hExp (eisensteinImaginaryContinuationBridge hMero hHolo eisensteinAbsoluteConvergence)

end Langlands.Global
