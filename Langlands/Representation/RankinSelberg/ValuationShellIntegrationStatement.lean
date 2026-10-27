import Langlands.LocalField.Normalization.Definitions
import Langlands.Representation.RankinSelberg.Measures
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Valuation-shell decomposition of normalized multiplicative Haar integrals

A derived interface for the valuation-shell route to the one-variable Mellin
argument of JPSS (1983), printed page 392. The unit group of a p-adic field is
the disjoint union of the shells of fixed normalized order, each a translate
of the integral units by a power of a uniformizer. The actual multiplicative
Haar integral of a continuous complex function is the sum of its shell
integrals. No part of the decomposition is proved here.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory

universe uF

/-- Shell geometry, local integrability, the integrability criterion and the
integral identity for the actual normalized multiplicative Haar measure.
The measure, the integral units and the shells are local to this proposition;
the uniformizer is an existential witness. -/
def ValuationShellIntegrationStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p)
    (T : F.TopologicalData),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    let μ : Measure F.Carrierˣ := localMultiplicativeHaar F.Carrier
    let K : Set F.Carrierˣ :=
      (integralUnits (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ)
    let S : ℤ → Set F.Carrierˣ := fun n => {a : F.Carrierˣ | T.ord (a : F.Carrier) = n}
    ∃ π : F.Carrierˣ, T.ord (π : F.Carrier) = 1 ∧
      -- shell geometry
      S 0 = K ∧
      Pairwise (fun m n : ℤ => Disjoint (S m) (S n)) ∧
      (⋃ n : ℤ, S n) = Set.univ ∧
      (∀ n : ℤ,
        S n = (fun u : F.Carrierˣ => π ^ n * u) '' K ∧
        IsOpen (S n) ∧ IsCompact (S n) ∧ MeasurableSet (S n) ∧
        μ (S n) = 1 ∧
        ∀ a ∈ S n, T.normalizedAbs (a : F.Carrier) =
          (T.residueCardinality : ℝ) ^ (-n)) ∧
      -- local integrability and the global integrability criterion
      (∀ f : F.Carrierˣ → ℂ, Continuous f →
        (∀ n : ℤ, IntegrableOn (fun u : F.Carrierˣ => f (π ^ n * u)) K μ) ∧
        (Integrable f μ ↔
          Summable (fun n : ℤ => ∫ u in K, ‖f (π ^ n * u)‖ ∂μ))) ∧
      -- the actual integral identity
      (∀ f : F.Carrierˣ → ℂ, Continuous f → Integrable f μ →
        Summable (fun n : ℤ => ∫ u in K, f (π ^ n * u) ∂μ) ∧
        (∫ a, f a ∂μ) = ∑' n : ℤ, ∫ u in K, f (π ^ n * u) ∂μ)

end Langlands.RankinSelberg
