import Langlands.Representation.RankinSelberg.UnequalRankComplementaryTransferProof
import Langlands.AllField.HarmonicAnalysis.PadicRowFourierCutoffProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankCompactSupportProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankComplementaryTransferStatement
import Langlands.AllField.Representation.RankinSelberg.UnequalRankFiniteExpansionProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankFourierSmearingProof
/-! Paired complementary-block transfer using one original-model coefficient.
Published support, coefficient integration, Fourier smearing, conjugation and
normalized cutoff results give both inner rectangular identities. These lift
to the actual iterated quotient integrals without a quotient-variable
interchange. Both real half-plane bounds can be chosen as zero. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.ComplementaryTransfer
open Langlands.RankinSelberg.ComplementaryTransfer hiding complementaryTransfer_of_row_cutoff exists_lower_average_and_dual_cutoff exists_lower_average_and_dual_cutoffAt exists_uniform_support_integrable
open Langlands.AllField.RankinSelberg.ComplementaryTransfer
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankCompactSupportStatement UnequalRankComplementaryTransferStatement UnequalRankFiniteExpansionStatement UnequalRankFourierSmearingStatement UnequalRankFunctionalEquationStatement UnequalRankIwasawaSupportStatement diagonal_abs_bound diagonal_abs_last exists_compactOpen_rectangular_subgroup normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply unequalRankCompactSupport unequalRankComplementaryTransfer unequalRankFiniteExpansion unequalRankFiniteExpansion_of_cosetExpansion unequalRankFourierSmearingStatement unequalRankIwasawaSupport unequalRank_coefficient_invariant
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement PadicRowFourierCutoffStatement padicRowFourierCutoff padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding SmoothSimpleRootSupportStatement smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear

universe uF uV uX uW

section FourierSign

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F] {d : ℕ}

end FourierSign

section SmallStabilizer

variable {G : Type*} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {X : Type uX} [TopologicalSpace X]

end SmallStabilizer

section ReflectedPlateau

variable {X : Type uX} [AddCommGroup X] [MeasurableSpace X] [MeasurableNeg X]

end ReflectedPlateau

section NormalizedCutoff

variable {X : Type uX} [MeasurableSpace X]

end NormalizedCutoff

section IteratedAssembly

variable {X : Type uX} [AddCommGroup X] [MeasurableSpace X] [MeasurableNeg X]
  {Y : Type*} [MeasurableSpace Y] {Z : Type*} [MeasurableSpace Z]

end IteratedAssembly

section RectangularAssembly

open Langlands.RankinSelberg.AdjacentBlockReduction

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F]

end RectangularAssembly

section RankTransport

open Langlands.RankinSelberg.AdjacentBlockReduction

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F]

end RankTransport

section UniformIntegrability

open Langlands.RankinSelberg.AdjacentBlockReduction

/-- The published uniform support theorem and the published coefficient
integration theorem discharge full rectangular integrability for the actual
supplied scalar Haar measure, before any quotient integral is considered. -/
theorem exists_uniform_support_integrable
    (F : Type uF) [Field F] (T : LocalFieldData F)
    (n r j k : ℕ) (hr : r = n + (j + k + 1)) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F),
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V,
      IsOfWhittakerType r (standardCharacter ψ r) π →
    ∀ (ℓ : glFunctionals ψ r π), ℓ.val ≠ 0 →
    ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∃ C : Set (Matrix (Fin j) (Fin (n + 1)) F),
        IsCompact C ∧
        (∀ g X, f.val.val (blockMatrixAt j k hr g X) ≠ 0 → X ∈ C) ∧
        ∀ g, Integrable (fun X => f.val.val (blockMatrixAt j k hr g X))
          (rectangularMeasure ν j (n + 1)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let : SigmaCompactSpace F := T.sigmaCompactSpace
  let : SecondCountableTopology F := T.secondCountableTopology
  let : BorelSpace (Matrix (Fin j) (Fin (n + 1)) F) :=
    inferInstanceAs (BorelSpace (Fin j → Fin (n + 1) → F))
  subst r
  intro ψ ν V _ _ π hπ ℓ hℓ f
  obtain ⟨C, hC, hs⟩ := unequalRankCompactSupport.{uF,uV} F T n j k ψ V π hπ ℓ hℓ f
  refine ⟨C, hC, hs, ?_⟩
  exact blockCoefficient_integrable ν n j k ψ π hπ.1.1 ℓ f C hC hs

end UniformIntegrability

section ActualIntegrals

open Langlands.RankinSelberg.AdjacentBlockReduction

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n r : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]

end ActualIntegrals

section DualAverage

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {r : ℕ} {X : Type uX} [MeasurableSpace X]

end DualAverage

section OneWitness

/-- Construct a single original-model witness using the published global and
pointwise Fourier-smearing theorem. The final assembly supplies the actual
matrix-conjugation premise. -/
theorem exists_lower_average_and_dual_cutoff
    (F : Type uF) [Field F] (T : LocalFieldData F)
    (n j k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F),
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ π : Representation ℂ
      (Langlands.GeneralLinear (n + ((k + 1) + j + 1) + 1) F) V,
      IsSmooth π →
    ∀ (ℓ : glFunctionals ψ (n + ((k + 1) + j + 1)) π)
      (f : (coefficientModel π ℓ).toSubmodule)
      (Φ κ : SchwartzBruhat (Fin (n + 1) → F)),
      IsRowFourierPair ψ ν Φ κ →
      (∀ x, κ (-x) = κ x) →
    ∀ (a : Langlands.GeneralLinear (n + ((k + 1) + j + 1) + 1) F)
      (L : (Fin (n + 1) → F) →
        Langlands.GeneralLinear (n + ((k + 1) + j + 1) + 1) F),
      (∀ x, inverseTranspose _ F
        (a⁻¹ * unequalRankSmearingUnipotent n k j x * a) = L x) →
    ∃ f₀ : (coefficientModel π ℓ).toSubmodule,
      (∀ h : Langlands.GeneralLinear (n + ((k + 1) + j + 1) + 1) F,
        Integrable (fun x => Φ x * f.val.val (h * L x)) (rowMeasure ν (n + 1)) ∧
        f₀.val.val h =
          ∫ x, Φ x * f.val.val (h * L x) ∂rowMeasure ν (n + 1)) ∧
      ∀ (g : Langlands.GeneralLinear (n + 1) F)
        (X : Matrix (Fin (k + 1)) (Fin (n + 1)) F),
        (translatedFirstDualModelEquiv ψ π ℓ a f₀).val.val
            (unequalRankMatrix (k + 1) j g X) =
          κ (X (Fin.last k)) *
            (translatedFirstDualModelEquiv ψ π ℓ a f).val.val
              (unequalRankMatrix (k + 1) j g X) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  intro ψ ν V _ _ π hπ ℓ f Φ κ hpair heven a L hUL
  have hsmear := unequalRankFourierSmearingStatement.{uF,uV} F T n k j
  let D := translatedFirstDualModelEquiv ψ π ℓ a
  have hinv := fourierPair_inverse_of_even ψ ν Φ κ hpair heven
  obtain ⟨g, hg, hcut⟩ := hsmear (ψ.scale (-1)) ν V (inverseTransposePullback π)
    (inverseTransposePullback_isSmooth π hπ) (firstDualFunctional ψ π ℓ) (D f)
    Φ κ hinv
  obtain ⟨f₀, hf₀, havg⟩ := exists_original_of_dual_average ψ
    (rowMeasure ν (n + 1)) Φ π ℓ a (unequalRankSmearingUnipotent n k j)
    L hUL f g hg
  refine ⟨f₀, havg, ?_⟩
  rw [hf₀]
  exact hcut

end OneWitness

section RankTransportWitness

open Langlands.RankinSelberg.AdjacentBlockReduction

/-- The single-witness construction at an arbitrary equal large rank. -/
theorem exists_lower_average_and_dual_cutoffAt
    (F : Type uF) [Field F] (T : LocalFieldData F)
    (n r j k : ℕ) (hr : r = n + ((k + 1) + j + 1)) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F),
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V,
      IsSmooth π →
    ∀ (ℓ : glFunctionals ψ r π) (f : (coefficientModel π ℓ).toSubmodule)
      (Φ κ : SchwartzBruhat (Fin (n + 1) → F)),
      IsRowFourierPair ψ ν Φ κ →
      (∀ x, κ (-x) = κ x) →
    ∀ (a : Langlands.GeneralLinear (r + 1) F)
      (L : (Fin (n + 1) → F) →
        Langlands.GeneralLinear (r + 1) F),
      (∀ x, inverseTranspose _ F
        (a⁻¹ * GeneralLinear.reindex (finCongr (by omega))
          (unequalRankSmearingUnipotent n k j x) * a) = L x) →
    ∃ f₀ : (coefficientModel π ℓ).toSubmodule,
      (∀ h : Langlands.GeneralLinear (r + 1) F,
        Integrable (fun x => Φ x * f.val.val (h * L x)) (rowMeasure ν (n + 1)) ∧
        f₀.val.val h =
          ∫ x, Φ x * f.val.val (h * L x) ∂rowMeasure ν (n + 1)) ∧
      ∀ (g : Langlands.GeneralLinear (n + 1) F)
        (X : Matrix (Fin (k + 1)) (Fin (n + 1)) F),
        (translatedFirstDualModelEquiv ψ π ℓ a f₀).val.val
            (blockMatrixAt (k + 1) j hr g X) =
          κ (X (Fin.last k)) *
            (translatedFirstDualModelEquiv ψ π ℓ a f).val.val
              (blockMatrixAt (k + 1) j hr g X) := by
  subst r
  simpa only [reindex_finCongr_rfl, MulEquiv.refl_apply, blockMatrixAt] using
    (exists_lower_average_and_dual_cutoff.{uF,uV} F T n j k)

end RankTransportWitness

section PairedAssembly

open Langlands.RankinSelberg.AdjacentBlockReduction

set_option backward.isDefEq.respectTransparency false in
/-- Assemble the paired transfer from a normalized row cutoff proposition.
The final theorem supplies this proposition by its published proof. -/
theorem complementaryTransfer_of_row_cutoff
    (F : Type uF) [Field F] (T : LocalFieldData F)
    (n r : ℕ) (hFourier : PadicRowFourierCutoffStatement F T (n + 1)) :
    UnequalRankComplementaryTransferStatement.{uF,uV,uW} F T n r := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let : SigmaCompactSpace F := T.sigmaCompactSpace
  let : SecondCountableTopology F := T.secondCountableTopology
  let : BorelSpace (Fin (n + 1) → F) := inferInstance
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro hnr ψ _ μ _ ν hν V _ _ W _ _ π σ hπ _ ℓ ℓ' hℓ _ j k hr f f'
  let : Measure.IsNegInvariant (rowMeasure ν (n + 1)) :=
    inferInstanceAs (Measure.IsNegInvariant (Measure.pi (fun _ : Fin (n + 1) => ν.measure)))
  have hr₁ : r = n + ((j + 1) + k + 1) := by omega
  have hr₂ : r = n + ((k + 1) + j + 1) := by omega
  obtain ⟨Cfull, hCfull, hs, hfull⟩ := exists_uniform_support_integrable.{uF,uV}
    F T n r (j + 1) k hr₁ ψ ν V π hπ ℓ hℓ f
  let C : Set (Fin (n + 1) → F) :=
    (fun X : Matrix (Fin (j + 1)) (Fin (n + 1)) F => X (Fin.last j)) '' Cfull
  have hC : IsCompact C := hCfull.image (continuous_apply (Fin.last j))
  let a := blockWeylAt (F := F) n r hnr
  let D := translatedFirstDualModelEquiv ψ π ℓ a
  let Ld : (Fin (n + 1) → F) → Langlands.GeneralLinear (r + 1) F :=
    fun x => GeneralLinear.reindex (finCongr (by omega))
      (rectangularUnipotent (k + 1) j (Fin.snoc 0 x))
  have hLd : Continuous Ld :=
    (continuous_reindex_finCongr (by omega)).comp (continuous_lastRowUnipotent n k j)
  have hLd₀ : Ld 0 = 1 := by
    have hz : (Fin.snoc 0 (0 : Fin (n + 1) → F) :
        Matrix (Fin (k + 1)) (Fin (n + 1)) F) = 0 := by
      ext b c
      induction b using Fin.lastCases <;> simp [Fin.snoc]
    simp only [Ld, hz, rectangularUnipotent_zero, map_one]
  obtain ⟨O, hO, hO₀, hfix⟩ := exists_open_coefficient_invariance
    (inverseTransposePullback π) (inverseTransposePullback_isSmooth π hπ.1.1)
    (firstDualFunctional ψ π ℓ) Ld hLd 0 hLd₀ (D f)
  obtain ⟨Φ, κ, hpair, hplateau, hsupp, hmass, hevenΦ, hevenκ⟩ :=
    hFourier ψ ν hν C hC O hO hO₀
  let L : (Fin (n + 1) → F) → Langlands.GeneralLinear (r + 1) F :=
    fun x => GeneralLinear.reindex (finCongr (by omega))
      (rectangularUnipotent (j + 1) k (Fin.snoc 0 (-x)))
  obtain ⟨f₀, havg, hcut⟩ := exists_lower_average_and_dual_cutoffAt.{uF,uV}
    F T n r j k hr₂ ψ ν V π hπ.1.1 ℓ f Φ κ hpair hevenκ a L
    (fun x => complementary_conjugationAt n r j k hr₁ hnr x)
  have horiginal := original_rectangular_transferAt n r j k hr₁ ν ψ
    f.val f₀.val Φ C (fun g X hX => ⟨X, hs g X hX, rfl⟩)
    hplateau hevenΦ hfull havg
  obtain ⟨_, _, _, hfulld⟩ := exists_uniform_support_integrable.{uF,uV}
    F T n r (k + 1) j hr₂ (ψ.scale (-1)) ν V (inverseTransposePullback π)
    (isOfWhittakerType_firstDual ψ π hπ) (firstDualFunctional ψ π ℓ)
    (firstDualFunctional_ne_zero ψ π hℓ) (D f₀)
  have hi : Integrable κ (rowMeasure ν (n + 1)) :=
    κ.continuous.integrable_of_hasCompactSupport κ.hasCompactSupport
  have hdual := cutoff_rectangular_transferAt n r k j hr₂ ν (ψ.scale (-1))
    (D f).val (D f₀).val κ hi hmass
    (fun x hx h => hfix x (hsupp hx) h) hcut hfulld
  refine ⟨f₀, 0, 0, ?_, ?_⟩
  · intro s _
    exact unequalRankIntegralAt_congr_inner (j + 1) k j (k + 1) hr₁ (by omega)
      ψ (normalizedAbsoluteValue T) μ
      (rectangularMeasure ν (j + 1) (n + 1)) (rectangularMeasure ν j (n + 1))
      f.val f₀.val f'.val horiginal s
  · intro s _
    exact (unequalRankIntegralAt_congr_inner (k + 1) j k (j + 1) hr₂ (by omega)
      (ψ.scale (-1)) (normalizedAbsoluteValue T) μ
      (rectangularMeasure ν (k + 1) (n + 1)) (rectangularMeasure ν k (n + 1))
      (D f₀).val (D f).val (secondDualFunction ψ n f'.val) hdual s).symm

end PairedAssembly

end Langlands.AllField.RankinSelberg.ComplementaryTransfer

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankCompactSupportStatement UnequalRankComplementaryTransferStatement UnequalRankFiniteExpansionStatement UnequalRankFourierSmearingStatement UnequalRankFunctionalEquationStatement UnequalRankIwasawaSupportStatement diagonal_abs_bound diagonal_abs_last exists_compactOpen_rectangular_subgroup normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply unequalRankCompactSupport unequalRankComplementaryTransfer unequalRankFiniteExpansion unequalRankFiniteExpansion_of_cosetExpansion unequalRankFourierSmearingStatement unequalRankIwasawaSupport unequalRank_coefficient_invariant
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement PadicRowFourierCutoffStatement padicRowFourierCutoff padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uV uW

/-- One coefficient in the original model transfers both actual original and
complementary dual integrals, with the supplied measures and independent
field and representation universes. -/
theorem unequalRankComplementaryTransfer
    (F : Type uF) [Field F] (T : LocalFieldData F)
    (n r : ℕ) : UnequalRankComplementaryTransferStatement.{uF,uV,uW} F T n r :=
  Langlands.AllField.RankinSelberg.ComplementaryTransfer.complementaryTransfer_of_row_cutoff F T n r
    (padicRowFourierCutoff F T (n + 1))

end Langlands.AllField.RankinSelberg
