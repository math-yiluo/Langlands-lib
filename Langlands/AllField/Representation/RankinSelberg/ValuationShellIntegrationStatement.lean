import Langlands.Representation.RankinSelberg.ValuationShellIntegrationStatement
import Langlands.AllField.LocalField.Foundation
/-!
# Valuation-shell decomposition of normalized multiplicative Haar integrals

A derived interface for the valuation-shell route to the one-variable Mellin
argument of JPSS (1983), printed page 392. The unit group of a nonarchimedean local
field, with supplied data `T : LocalFieldData F`, is the disjoint union of the shells
of fixed normalized order, each a translate of the integral units by a power of a
uniformizer. The actual multiplicative
Haar integral of a continuous complex function is the sum of its shell
integrals. No part of the decomposition is proved here.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding ValuationShellIntegrationStatement
open Langlands.AllField.RankinSelberg

open MeasureTheory

universe uF

/-- Shell geometry, local integrability, the integrability criterion and the
integral identity for the actual normalized multiplicative Haar measure.
The measure, the integral units and the shells are local to this proposition;
the uniformizer is an existential witness. -/
def ValuationShellIntegrationStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI := borel Fˣ
    letI : BorelSpace Fˣ := ⟨rfl⟩
    let μ : Measure Fˣ := localMultiplicativeHaar F
    let K : Set Fˣ :=
      (integralUnits (ValuativeRel.valuation F).integer : Set Fˣ)
    let S : ℤ → Set Fˣ := fun n => {a : Fˣ | T.ord (a : F) = n}
    ∃ π : Fˣ, T.ord (π : F) = 1 ∧
      -- shell geometry
      S 0 = K ∧
      Pairwise (fun m n : ℤ => Disjoint (S m) (S n)) ∧
      (⋃ n : ℤ, S n) = Set.univ ∧
      (∀ n : ℤ,
        S n = (fun u : Fˣ => π ^ n * u) '' K ∧
        IsOpen (S n) ∧ IsCompact (S n) ∧ MeasurableSet (S n) ∧
        μ (S n) = 1 ∧
        ∀ a ∈ S n, T.normalizedAbs (a : F) =
          (T.residueCardinality : ℝ) ^ (-n)) ∧
      -- local integrability and the global integrability criterion
      (∀ f : Fˣ → ℂ, Continuous f →
        (∀ n : ℤ, IntegrableOn (fun u : Fˣ => f (π ^ n * u)) K μ) ∧
        (Integrable f μ ↔
          Summable (fun n : ℤ => ∫ u in K, ‖f (π ^ n * u)‖ ∂μ))) ∧
      -- the actual integral identity
      (∀ f : Fˣ → ℂ, Continuous f → Integrable f μ →
        Summable (fun n : ℤ => ∫ u in K, f (π ^ n * u) ∂μ) ∧
        (∫ a, f a ∂μ) = ∑' n : ℤ, ∫ u in K, f (π ^ n * u) ∂μ)

end Langlands.AllField.RankinSelberg
