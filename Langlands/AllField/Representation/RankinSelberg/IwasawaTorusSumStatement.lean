import Langlands.Representation.RankinSelberg.IwasawaTorusSumStatement
import Langlands.AllField.Group.GL.Padic
/-!
# Discrete torus decomposition of the normalized Iwasawa pushforward

This is an internal measure identity for the torus and compact factors.
It is stated independently of any compatible quotient measure or quotient
Iwasawa integration formula. This module does not prove the identity.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding IwasawaTorusSumStatement
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF

/-- The inverse-modulus-weighted torus/compact pushforward is the countable
sum of the compact pushforwards at all uniformizer exponent vectors.
The supplied Haar normalizations give scalar one. -/
def IwasawaTorusSumStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ),
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
  ∀ ϖ : Fˣ,
    Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ →
  let A := Fin (n + 1) → Fˣ
  let G := Langlands.GeneralLinear (n + 1) F
  let Q := LeftUnipotentQuotient n F
  let da : Measure A := Measure.pi (fun _ : Fin (n + 1) =>
    localMultiplicativeHaar F)
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
  let dk : Measure G := (generalLinearHaar F n).restrict (K : Set G)
  let δ : A → ℝ := fun a =>
    ∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
      T.normalizedAbs ((a i / a j : Fˣ) : F)
  let q : A × G → Q := fun x =>
    leftQuotientMap (upperUnipotent (n + 1) F)
      (Iwasawa.diagonalUnits x.1 * x.2)
  let t : (Fin (n + 1) → ℤ) → A := fun lam i => ϖ ^ lam i
  let qLam : (Fin (n + 1) → ℤ) → G → Q := fun lam k =>
    leftQuotientMap (upperUnipotent (n + 1) F)
      (Iwasawa.torus ϖ lam * k)
  Measure.map q ((da.prod dk).withDensity (fun x => ENNReal.ofReal ((δ x.1)⁻¹))) =
    Measure.sum (fun lam : Fin (n + 1) → ℤ =>
      ENNReal.ofReal ((δ (t lam))⁻¹) • Measure.map (qLam lam) dk)

end Langlands.AllField.RankinSelberg
