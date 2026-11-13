import Langlands.Representation.RankinSelberg.QuotientIwasawaIntegrationStatement
import Langlands.AllField.Group.GL.Padic
/-!
# Normalized quotient Iwasawa integration

This proposition states the measure identity underlying JPSS Theorem 2.7,
printed p391, equation (3). It uses ordinary diagonal entries and the published
mass-one Haar normalizations. It does not prove the integration formula.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding QuotientIwasawaIntegrationStatement
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF

/-- Every compatible measure on the actual left-unipotent quotient is the
pushforward of diagonal Haar times the restricted compact Haar, weighted by
the inverse upper-Borel modulus. No integrability hypothesis is imposed. -/
def QuotientIwasawaIntegrationStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel Fˣ
  letI : BorelSpace Fˣ := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F)
  letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F)
  letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  let A := Fin (n + 1) → Fˣ
  let da : Measure A := Measure.pi (fun _ : Fin (n + 1) =>
    localMultiplicativeHaar F)
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
  let dk := (generalLinearHaar F n).restrict (K : Set _)
  let δ : A → ℝ := fun a =>
    ∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
      T.normalizedAbs ((a i / a j : Fˣ) : F)
  let q : A × Langlands.GeneralLinear (n + 1) F →
      LeftUnipotentQuotient n F := fun x =>
    leftQuotientMap (upperUnipotent (n + 1) F)
      (Iwasawa.diagonalUnits x.1 * x.2)
  ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F),
      IsCompatible (upperUnipotent (n + 1) F)
        (generalLinearHaar F n) (unipotentHaar F n) μ →
      μ = Measure.map q
        ((da.prod dk).withDensity (fun x => ENNReal.ofReal ((δ x.1)⁻¹)))

end Langlands.AllField.RankinSelberg
