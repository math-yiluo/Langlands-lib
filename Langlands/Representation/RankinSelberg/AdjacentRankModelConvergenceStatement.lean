import Langlands.Representation.RankinSelberg.AdjacentRankIntegralModel

/-!
# Unconditional convergence of the JPSS Section 6.1 tensor integral

This is the convergence assertion of the Proposition in JPSS Section 6.1,
printed pp.428–429, for formula (8). It uses the published special lower-block
model unchanged and quantifies over the entire algebraic tensor test space.
The large-positive-twist restriction concerns the separate induced-model
spanning assertion. This module defines an unproved proposition.
-/

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker

universe uF uV

/-- JPSS Section 6.1, formula (8): every test tensor has an integrable scalar
integrand at every ambient element, for every quasicharacter and every supplied
self-dual scalar Haar measure, when the inner representation has full standard
Whittaker type. The conclusion uses exactly the canonical p-adic model and its
shared Haar measure. This definition supplies no convergence proof. -/
def AdjacentRankModelConvergenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    haveI : BorelSpace F.Carrier := ⟨rfl⟩
    haveI : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
    haveI : TotallyDisconnectedSpace F.Carrier := by
      let : NonarchimedeanRing F.Carrier := by
        convert! ValuativeRel.nonarchimedeanRing F.Carrier
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (ν : AdditiveHaarMeasure F.Carrier) (hself : IsSelfDual ψ ν)
      (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V),
      IsOfWhittakerType r (standardCharacter ψ r) σ →
      ∀ (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)
        (Ψ : adjacentRankTestSpace ψ σ ℓ) (g : GeneralLinear (r + 2) F.Carrier),
        Padic.AdjacentRankModelConverges F ψ ν hself σ ℓ χ Ψ g

end Langlands.RankinSelberg
