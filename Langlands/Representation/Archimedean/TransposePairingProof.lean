import Langlands.HarmonicAnalysis.Distribution.RealTransposeInvariantProof
import Langlands.Representation.Archimedean.ComplexTransposePairingProof
import Langlands.Representation.Archimedean.RealFrobeniusCharacter
import Langlands.Representation.Archimedean.RealPrincipalSeriesSubrepresentationProof
import Langlands.Representation.Archimedean.RealTransposePairingFromTrace
import Langlands.Representation.Archimedean.TransposeHaar

/-! # Archimedean inverse-transpose pairing -/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace Matrix Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open RealPrincipalSeriesHilbert RealPrincipalSeriesDuality
open Langlands.HarmonicAnalysis.RealGeneralLinearDistribution

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] RealPrincipalSeriesDuality.measurableSpaceK RealPrincipalSeriesDuality.borelSpaceK

universe uV

local instance realGLSecondCountable (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  Units.isOpenEmbedding_val.secondCountableTopology

local instance realGLLocallyCompact (n : ℕ) : LocallyCompactSpace (Langlands.GeneralLinear n ℝ) :=
  Units.isOpenEmbedding_val.locallyCompactSpace

set_option maxHeartbeats 1700000 in
/-- The real inverse-transpose pairing through the Frobenius character. -/
theorem realTransposePairing : RealTransposePairingStatement.{uV} := by
  intro r V _ _ ρ π hgk hirr hadm
  let n := r + 1
  have hj := realJacquetModuleFinite_of_finiteDimensional_of_nonvanishing
    (realJacquetFiniteDimensional_of_finiteGeneration
      RealJacquetFiniteGeneration.realJacquetFiniteGeneration)
    (RealJacquetNonvanishing.realJacquetNonvanishingSubquotientReduction realPrincipalSeriesSubquotient)
  obtain ⟨hfin, hne⟩ := hj n V ρ π hgk hirr hadm
  obtain ⟨ℓ, a, eps, h₀, hℓ⟩ := exists_isRealJacquetFunctional hgk hfin hne
  obtain ⟨e, hG⟩ := exists_frobeniusEquiv_globalization hgk hℓ hirr hadm h₀
  let G := Langlands.GeneralLinear n ℝ
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let μ : Measure G := Measure.haar
  let : μ.IsHaarMeasure := by dsimp [μ]; infer_instance
  let : μ.Regular := by dsimp [μ]; infer_instance
  let : μ.IsMulRightInvariant := isMulRightInvariant_archimedeanGL ℝ n μ
  let : SFinite μ := by
    have : SigmaFinite μ := inferInstance
    infer_instance
  let ν := haarK n
  let : ν.Regular := by dsimp [ν, haarK]; infer_instance
  let : ν.IsInvInvariant := Langlands.isInvInvariant_of_isMulRightInvariant ν
  let W := (frobeniusClosure hgk hℓ : Type)
  let R := frobeniusClosureRepresentation hgk hℓ
  let wNorm : NormedAddCommGroup W := Submodule.normedAddCommGroup (frobeniusClosure hgk hℓ)
  let wInner : InnerProductSpace ℂ W := Submodule.innerProductSpace (frobeniusClosure hgk hℓ)
  have wComplete : CompleteSpace W := (isClosed_frobeniusClosure hgk hℓ).isComplete.completeSpace_coe
  let D := frobeniusCharacter hgk hℓ μ
  have hinv : IsTransposeInvariant D := Langlands.realGeneralLinearConjugationDistributionTranspose
    r D (isConjugationInvariant_frobeniusCharacter hgk hℓ μ)
  let compareTrace := @traceClass_and_trace_transpose_of_realHilbertCharacter n _ _ μ _
    W wNorm wInner wComplete R hG.1.1
  let hKernel := compareTrace (isTraceClass_frobeniusRealTestOperator hgk hℓ μ) hinv
  let pairing := @hasRealTransposePairing_of_smoothKernelTrace n _ _ μ _ _ _ _ _ ν _ _ _
    W wNorm wInner wComplete R
  exact @pairing V ‹AddCommGroup V› ‹Module ℂ V› ρ π e hgk hirr hadm hG
    (inner_frobeniusClosureRepresentation_compact hgk hℓ) hKernel

/-- Every irreducible admissible real or complex GK module of positive matrix
size admits a nonzero inverse-transpose invariant pairing. -/
theorem archimedeanTransposePairing : ArchimedeanTransposePairingStatement.{uV} :=
  ⟨realTransposePairing, complexTransposePairing⟩

end Langlands.Archimedean
