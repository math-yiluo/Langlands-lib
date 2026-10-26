import Langlands.Representation.RankinSelberg.QuotientIntegrals
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.Whittaker.Iwasawa
import Langlands.Analysis.Local.QuotientTopology
import Langlands.LocalField.Normalization.Proof
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Discrete torus decomposition of the normalized Iwasawa pushforward

This is an internal measure identity for the torus and compact factors.
It is stated independently of any compatible quotient measure or quotient
Iwasawa integration formula. This module does not prove the identity.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear QuotientIntegration

universe uF

/-- The inverse-modulus-weighted torus/compact pushforward is the countable
sum of the compact pushforwards at all uniformizer exponent vectors.
The supplied Haar normalizations give scalar one. -/
def IwasawaTorusSumStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ),
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F.Carrierˣ
  letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ ϖ : F.Carrierˣ,
    Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ →
  let A := Fin (n + 1) → F.Carrierˣ
  let G := Langlands.GeneralLinear (n + 1) F.Carrier
  let Q := LeftUnipotentQuotient n F.Carrier
  let da : Measure A := Measure.pi (fun _ : Fin (n + 1) =>
    localMultiplicativeHaar F.Carrier)
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let dk : Measure G := (generalLinearHaar F.Carrier n).restrict (K : Set G)
  let δ : A → ℝ := fun a =>
    ∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
      T.normalizedAbs ((a i / a j : F.Carrierˣ) : F.Carrier)
  let q : A × G → Q := fun x =>
    leftQuotientMap (upperUnipotent (n + 1) F.Carrier)
      (Iwasawa.diagonalUnits x.1 * x.2)
  let t : (Fin (n + 1) → ℤ) → A := fun lam i => ϖ ^ lam i
  let qLam : (Fin (n + 1) → ℤ) → G → Q := fun lam k =>
    leftQuotientMap (upperUnipotent (n + 1) F.Carrier)
      (Iwasawa.torus ϖ lam * k)
  Measure.map q ((da.prod dk).withDensity (fun x => ENNReal.ofReal ((δ x.1)⁻¹))) =
    Measure.sum (fun lam : Fin (n + 1) → ℤ =>
      ENNReal.ofReal ((δ (t lam))⁻¹) • Measure.map (qLam lam) dk)

end Langlands.RankinSelberg
