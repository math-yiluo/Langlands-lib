import Langlands.Representation.RankinSelberg.UnequalRankCompactPairingFunctionals
import Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicPairingStatement
import Langlands.AllField.Representation.Whittaker.MirabolicCompactTwistedPairingProof
/-!
# Unequal-rank compact pairings and inverse-standard Whittaker functionals

For `n < r`, the unequal-rank covariant forms on the compact mirabolic model of rank
`r + 1` against a smooth representation `η` of `GL_(n+1)` embed linearly into the
inverse-standard Whittaker functionals of `η`, and there is a nonzero form as soon as `η`
has a nonzero such functional. The proof reduces `r` to `n + 1` by restriction along the
successor embedding and identifies the adjacent-rank forms with invariant forms on
`c-Ind_N^(GL_(n+1)) θ × η`. Consequently the form space is a line whenever the
inverse-standard Whittaker functionals of `η` form a line.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankBilinearUniquenessStatement UnequalRankCommonGeneratorStatement UnequalRankCompactGenericPairingStatement UnequalRankMirabolicPairingRigidityStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open MeasureTheory Topology
open Langlands.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicFunctionalMultiplicityStatement
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open scoped ENNReal

universe uF uW

namespace UnequalRankCompactPairing
open Langlands.RankinSelberg.UnequalRankCompactPairing hiding nonempty_equiv_complex_padic
open Langlands.AllField.RankinSelberg.UnequalRankCompactPairing
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankBilinearUniquenessStatement UnequalRankCommonGeneratorStatement UnequalRankCompactGenericPairingStatement UnequalRankMirabolicPairingRigidityStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

section Generic

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [∀ m, NonarchimedeanGroup (Langlands.GeneralLinear m F)]
  [∀ m, LocallyCompactSpace (Langlands.GeneralLinear m F)]
variable (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {n : ℕ} (η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)

variable [MeasurableSpace (QuotientIntegration.LeftQuotient (GeneralLinear.upperUnipotent (n + 1) F))]
  [BorelSpace (QuotientIntegration.LeftQuotient (GeneralLinear.upperUnipotent (n + 1) F))]
  (ν : Measure (QuotientIntegration.LeftQuotient (GeneralLinear.upperUnipotent (n + 1) F)))

end Generic

/-- For a nonarchimedean local field with the topology of the supplied data `T`, the
unequal-rank forms on the actual compact mirabolic model against a smooth
representation `η` with a nonzero inverse-standard Whittaker functional form a line,
provided the inverse-standard Whittaker functionals of `η` form a line. -/
theorem nonempty_equiv_complex_padic (F : Type uF) [Field F]
    (T : LocalFieldData F) (n r : ℕ) :
    letI := T.topology
    letI : IsTopologicalRing F := by
      let := T.valuativeRel
      let := T.localField
      infer_instance
    ∀ hnr : n < r,
    ∀ ψ : UnitaryAdditiveCharacter F,
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
    ∀ η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W,
      IsSmooth η →
      Whittaker.HasFunctional
        (N := GeneralLinear.upperUnipotent (n + 1) F)
        (θ := Whittaker.inverseStandardCharacter ψ n) η →
      (∀ ℓ₁ ℓ₂ : Whittaker.functionals (GeneralLinear.upperUnipotent (n + 1) F)
        (inverseStandardCharacter ψ n) η, ℓ₁.val ≠ 0 → ∃ c : ℂ, ℓ₂ = c • ℓ₁) →
      ∀ s : ℂ,
        Nonempty
          ((unequalRankMirabolicForms hnr ψ (normalizedAbsoluteValue T)
            (Whittaker.mirabolicCompactInduced ψ r) η s) ≃ₗ[ℂ] ℂ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.fieldT2
  have := MirabolicCompactTwistedPairing.valuative_nonarchimedean (K := F)
  have : ∀ m, NonarchimedeanGroup (Langlands.GeneralLinear m F) :=
    T.generalLinearNonarchimedean
  have : ∀ m, LocallyCompactSpace (Langlands.GeneralLinear m F) :=
    T.generalLinearLocallyCompactSpace
  intro hnr ψ W _ _ η hη hWh hline s
  have hker : IsOpen ((standardCharacter ψ n).ker :
      Set (GeneralLinear.upperUnipotent (n + 1) F)) := by
    have := T.upperUnipotentNonarchimedean (n + 1)
    exact isOpen_ker_of_continuous_complex_character _ (standardCharacterContinuous ψ n).continuous
  let : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
  have : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) F) := borel _
  have : BorelSpace (GeneralLinear.upperUnipotent (n + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (QuotientIntegration.LeftQuotient
      (GeneralLinear.upperUnipotent (n + 1) F)) := borel _
  have : BorelSpace (QuotientIntegration.LeftQuotient
      (GeneralLinear.upperUnipotent (n + 1) F)) := ⟨rfl⟩
  have hν := unipotentQuotientHaar_isCompatible F n
  have : IsFiniteMeasureOnCompacts (unipotentQuotientHaar F n) := inferInstance
  exact nonempty_equiv_complex ψ (normalizedAbsoluteValue T) η (unipotentQuotientHaar F n)
    (MirabolicWhittaker.isOpen_complex_eq_one ψ)
    (MirabolicCompactTwistedPairing.isOpenNormOne_normalizedAbsoluteValue T) hker
    hν.right_invariant hν.compactOpenQuotientOrbit_mass hη hWh hline hnr s

end UnequalRankCompactPairing

end Langlands.AllField.RankinSelberg
