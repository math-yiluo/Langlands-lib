import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.RankinSelberg.DeterminantSlices
import Mathlib.Analysis.Analytic.Basic

/-!
# Entire dependence of corank-one determinant-slice coefficients

A derived prerequisite extracted from the uniform-level and determinant-slice
argument of JPSS (1983), Section 4.5, printed pages 408–409, in the corank-one
setting relevant to Section 6.1/6.3, printed pages 427–438. This module defines
the proposition only; it does not prove integrability or analyticity.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

/-- Every determinant slice of a common-level, pointwise entire family of
standard Whittaker functions on `GL_(r+2)`, paired with a fixed inverse-character
coefficient of a full Whittaker-type representation on `GL_(r+1)`, is integrable
and has an entire coefficient. This is a closed proposition, not a proof. -/
def CorankOneEntireSliceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (r : ℕ),
      letI := borel (Langlands.GeneralLinear (r + 1) F.Carrier)
      letI : BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
      letI := borel (upperUnipotent (r + 1) F.Carrier)
      letI : BorelSpace (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
      letI := borel (LeftUnipotentQuotient r F.Carrier)
      letI : BorelSpace (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩
      ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)],
      ∀ ν : Measure (LeftUnipotentQuotient r F.Carrier),
        IsCompatible (upperUnipotent (r + 1) F.Carrier)
          (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν →
        ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
          (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V),
          IsOfWhittakerType r (inverseStandardCharacter ψ r) τ →
          ∀ (ℓ : glInverseFunctionals ψ r τ)
            (Wprime : (coefficientModel τ ℓ).toSubmodule)
            (U : ℂ → WhittakerFunctions ψ (r + 1)),
            (∃ K : Subgroup (Langlands.GeneralLinear (r + 1 + 1) F.Carrier),
              IsOpen (K : Set (Langlands.GeneralLinear (r + 1 + 1) F.Carrier)) ∧
              IsCompact (K : Set (Langlands.GeneralLinear (r + 1 + 1) F.Carrier)) ∧
              ∀ (u : ℂ) (g : Langlands.GeneralLinear (r + 1 + 1) F.Carrier) (k : K),
                (U u).val (g * k) = (U u).val g) →
            (∀ (g : Langlands.GeneralLinear (r + 1 + 1) F.Carrier) (u : ℂ),
              AnalyticAt ℂ (fun z => (U z).val g) u) →
            ∀ m : ℤ,
              (∀ u : ℂ,
                SliceIntegrableAt F.canonicalTopologicalData ν
                  (corankOneIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
                    (U u) Wprime.val 0) m) ∧
              ∀ u : ℂ,
                AnalyticAt ℂ
                  (fun z => sliceCoefficient F.canonicalTopologicalData ν
                    (corankOneIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
                      (U z) Wprime.val 0) m) u

end Langlands.RankinSelberg
