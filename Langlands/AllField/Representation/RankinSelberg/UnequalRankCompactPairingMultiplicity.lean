import Langlands.Representation.RankinSelberg.UnequalRankCompactPairingMultiplicity
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.AllField.Representation.RankinSelberg.UnequalRankCompactPairingFunctionals
import Langlands.AllField.Representation.Whittaker.MultiplicityOneStatement
import Langlands.Representation.Whittaker.LocalFieldMultiplicityOneProof
/-!
# The unequal-rank compact generic pairing from Whittaker multiplicity one

The Library theorem `Langlands.Whittaker.localFieldMultiplicityOne` (Whittaker multiplicity
one over every nonarchimedean local field) gives `MultiplicityOneStatement` for bundled
local-field data, and hence multiplicity one for the inverse standard character under the
supplied topology. Combined with the line criterion of `UnequalRankCompactPairingFunctionals`,
it gives the exact-dimension statement `UnequalRankCompactGenericPairingStatement`.
-/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding MultiplicityOneStatement

universe uF uV

/-- Whittaker multiplicity one in the form of `MultiplicityOneStatement` (bundled local-field
data `T`), obtained from the Library theorem `Langlands.Whittaker.localFieldMultiplicityOne`
for the instances packaged in `T`. -/
theorem multiplicityOne : MultiplicityOneStatement.{uF, uV} := by
  intro F _ T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro n V _ _ ψ π hadm hirr ℓ₁ ℓ₂ h
  exact Langlands.Whittaker.localFieldMultiplicityOne F n V ψ π hadm hirr ℓ₁ ℓ₂ h

end Langlands.AllField.Whittaker

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankBilinearUniquenessStatement UnequalRankCommonGeneratorStatement UnequalRankCompactGenericPairingStatement UnequalRankFunctionalEquationStatement UnequalRankMirabolicPairingRigidityStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicFunctionalMultiplicityStatement MultiplicityOneStatement
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear

universe uF uW

namespace UnequalRankCompactPairing
open Langlands.RankinSelberg.UnequalRankCompactPairing hiding inverseFunctionals_line_of_multiplicityOne nonempty_equiv_complex_padic unequalRankCompactGenericPairing_of_multiplicityOne
open Langlands.AllField.RankinSelberg.UnequalRankCompactPairing
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankBilinearUniquenessStatement UnequalRankCommonGeneratorStatement UnequalRankCompactGenericPairingStatement UnequalRankFunctionalEquationStatement UnequalRankMirabolicPairingRigidityStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

/-- Whittaker multiplicity one for the inverse standard character under the supplied
topology of a nonarchimedean local field. -/
theorem inverseFunctionals_line_of_multiplicityOne
    (hmult : Whittaker.MultiplicityOneStatement.{uF, uW})
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) :
    letI := T.topology
    ∀ ψ : UnitaryAdditiveCharacter F,
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
    ∀ η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W,
      IsAdmissible η → Representation.IsIrreducible η →
      ∀ ℓ₁ ℓ₂ : Whittaker.functionals (GeneralLinear.upperUnipotent (n + 1) F)
        (inverseStandardCharacter ψ n) η, ℓ₁.val ≠ 0 → ∃ c : ℂ, ℓ₂ = c • ℓ₁ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ W _ _ η hadm hirr ℓ₁ ℓ₂ h1
  have hχ := Langlands.RankinSelberg.standardCharacter_scale_neg_one ψ n
  have m₁ : ℓ₁.val ∈ glFunctionals (ψ.scale (-1)) n η := by
    rw [glFunctionals, hχ]
    exact ℓ₁.property
  have m₂ : ℓ₂.val ∈ glFunctionals (ψ.scale (-1)) n η := by
    rw [glFunctionals, hχ]
    exact ℓ₂.property
  obtain ⟨c, hc, -⟩ := hmult F T n W (ψ.scale (-1)) η hadm hirr
    ⟨ℓ₁.val, m₁⟩ ⟨ℓ₂.val, m₂⟩ h1
  have hv : ℓ₂.val = c • ℓ₁.val := congrArg Subtype.val hc
  exact ⟨c, Subtype.ext hv⟩

/-- Whittaker multiplicity one implies the exact-dimension statement for the unequal-rank
compact generic pairing. -/
theorem unequalRankCompactGenericPairing_of_multiplicityOne
    (hmult : Whittaker.MultiplicityOneStatement.{uF, uW})
    (F : Type uF) [Field F] (T : LocalFieldData F) (n r : ℕ) :
    UnequalRankCompactGenericPairingStatement.{uF, uW} F T n r := by
  intro hnr ψ W _ _ η hadm hirr hWh s
  exact nonempty_equiv_complex_padic F T n r hnr ψ W η hadm.1 hWh
    (inverseFunctionals_line_of_multiplicityOne hmult F T n ψ W η hadm hirr) s

end UnequalRankCompactPairing

end Langlands.AllField.RankinSelberg
