import Langlands.Representation.RankinSelberg.UnitaryContragredientTwistParameters
import Langlands.Representation.RankinSelberg.SupercuspidalPairPoleOrder
import Langlands.LocalFactor.Analytic.FiniteUnitaryEuler

/-! # Actual L-polynomial and analytic adapters for unitary supercuspidal pairs -/

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial GeneralLinear HarmonicAnalysis Whittaker

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W}

namespace UnitaryContragredientTwistParameterSet

variable (U : UnitaryContragredientTwistParameterSet F π σ)

/-- The exact twist set, with the actual residue cardinality as spectral base. -/
def eulerData : LocalFactor.FiniteUnitaryEuler where
  q := F.canonicalTopologicalData.residueCardinality
  q_gt_one := by exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
  parameters := U.parameters
  norm_eq_one := U.norm_eq_one

/-- The exact matched-pair test for the Euler parameter one. -/
theorem one_mem_iff :
    (1 : ℂ) ∈ U.eulerData.parameters ↔
      letI := F.canonicalTopologicalData.topology
      haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup (r + 1)
      Nonempty (π.Equiv (smoothContragredient σ)) :=
  one_mem_iff_of_supercuspidalTwistSet U.mem_iff

/-- JPSS's equal-rank formula certifies this exact finite Euler polynomial.
The representation-theoretic formula remains an explicit premise. -/
theorem isPadicPairLPolynomial
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, uV, uW})
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (hπ : π.IsIrreducible)
    (hπs : letI := F.canonicalTopologicalData.topology; IsSupercuspidal π)
    (hσ : σ.IsIrreducible)
    (hσw : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) σ) :
    IsPadicPairLPolynomial F ψ ν.val π σ U.eulerData.polynomial := by
  classical
  obtain ⟨A, hA, hP⟩ := hEq p F ψ ν r π σ hπ hπs hσ hσw
  have hAU : A = U.parameters := by
    ext a
    exact (hA a).trans (U.mem_iff a).symm
  change IsPadicPairLPolynomial F ψ ν.val π σ (∏ a ∈ U.parameters, (1 - C a * X))
  rw [← hAU]
  exact hP

/-- Uniqueness identifies the actual reciprocal evaluation of every certified
pair polynomial with the finite Euler reciprocal. -/
theorem reciprocal_eq_of_certified
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier}
    (hE : IsPadicPairLPolynomial F ψ ν π σ U.eulerData.polynomial)
    {P : ℂ[X]} (hP : IsPadicPairLPolynomial F ψ ν π σ P) (s : ℂ) :
    U.eulerData.reciprocal s =
      (P.eval (spectralPoint F.canonicalTopologicalData.residueCardinality s))⁻¹ := by
  rw [hP.unique hE]
  change (U.eulerData.denominator s)⁻¹ = _
  rw [U.eulerData.denominator_eq_eval,
    spectralPoint_eq_spectralParameter _ (lt_trans zero_lt_one U.eulerData.q_gt_one)]
  rfl

/-- The analytic pole conditions hold for the actual certified function. -/
theorem analytic_conditions_of_certified
    {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
    {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier}
    (hE : IsPadicPairLPolynomial F ψ ν π σ U.eulerData.polynomial)
    {P : ℂ[X]} (hP : IsPadicPairLPolynomial F ψ ν π σ P) :
    let L : ℂ → ℂ := fun s =>
      (P.eval (spectralPoint F.canonicalTopologicalData.residueCardinality s))⁻¹
    (∀ s, MeromorphicAt L s ∧ meromorphicOrderAt L s ≤ 0) ∧
      (∀ s, s.re ≠ 0 → Global.PoleComparison.HolomorphicUnitAt L s) ∧
      ((letI := F.canonicalTopologicalData.topology
        haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup (r + 1)
        Nonempty (π.Equiv (smoothContragredient σ))) → meromorphicOrderAt L 0 < 0) := by
  have hL : (fun s =>
      (P.eval (spectralPoint F.canonicalTopologicalData.residueCardinality s))⁻¹) =
      U.eulerData.reciprocal := by
    funext s
    exact (U.reciprocal_eq_of_certified hE hP s).symm
  change (∀ s, MeromorphicAt _ s ∧ meromorphicOrderAt _ s ≤ 0) ∧ _
  rw [hL]
  exact ⟨fun s => ⟨U.eulerData.meromorphicAt_reciprocal s,
      U.eulerData.reciprocal_order_nonpos s⟩,
    fun _ hs => U.eulerData.holomorphicUnitAt_reciprocal hs,
    fun he => U.eulerData.reciprocal_order_zero_neg (U.one_mem_iff.mpr he)⟩

end UnitaryContragredientTwistParameterSet
end Langlands.RankinSelberg
