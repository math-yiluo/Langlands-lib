import Langlands.Representation.RankinSelberg.AnalyticTemperedLFactor
import Langlands.Representation.RankinSelberg.TemperedLFactorDivisibility
import Langlands.Representation.RankinSelberg.LanglandsQuotientLFactorStatement

/-!
# Certified polynomials and residuals for actual Langlands standard modules

Full Whittaker type follows from the analytic tempered blocks and their real
twists. Finite L-divisibility then constructs all polynomial witnesses and a
normalized residual for the unchanged standard modules.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker Polynomial GeneralLinear
open PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology;
    UnitaryAdditiveCharacter F.Carrier)

/-- Real determinant twists of irreducible analytic tempered actions have full
standard Whittaker type on their original carriers. -/
theorem analyticTemperedRealTwistWhittakerType {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hiπ : Representation.IsIrreducible π)
    (htπ : F.canonicalTopologicalData.IsTempered π) (s : ℝ) :
    letI := F.canonicalTopologicalData.topology;
    IsOfWhittakerType r (standardCharacter ψ r)
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm (r + 1)) s π) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  apply (isOfWhittakerType_twist_iff (standardCharacter ψ r)
    (T.determinantPowerCharacter (r + 1) s) π
    (T.isOpen_ker_determinantPowerCharacter (r + 1) s) ?_).mpr
    (analyticTemperedWhittakerType F ψ π hiπ htπ)
  intro u
  exact (ker_le_realPowerCharacter_ker (T.determinantNorm (r + 1)) s)
    (TwoBlockDeformation.determinantNorm_eq_one_of_mem_upperUnipotent F T u.property)

/-- Full standard Whittaker type of the actual normalized upper standard
module of any genuine tempered Langlands datum. -/
theorem langlandsStandardModuleWhittakerType {r : ℕ}
    (d : TemperedLanglandsDatum.{uV,uF} F.canonicalTopologicalData (r + 1)) :
    letI := F.canonicalTopologicalData.topology;
    IsOfWhittakerType r (standardCharacter ψ r) d.standardModule.representation := by
  let := F.canonicalTopologicalData.topology
  rcases d with ⟨⟨k, size, pos, total⟩, π, hiπ, htπ, s, hs⟩
  obtain ⟨m, rfl⟩ : ∃ m : Fin k → ℕ, size = fun i => m i + 1 :=
    ⟨fun i => size i - 1, funext fun i => (Nat.sub_add_cancel (pos i)).symm⟩
  exact normalizedProductWhittakerType p F ψ r k m total
    (fun i => (F.canonicalTopologicalData.segmentFactor (π i) (s i)).representation)
    (fun i => analyticTemperedRealTwistWhittakerType F ψ
      (π i).representation (hiπ i) (htπ i) (s i))

variable (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {r t : ℕ}
  (d : TemperedLanglandsDatum.{uV,uF} F.canonicalTopologicalData (r + 1))
  (e : TemperedLanglandsDatum.{uW,uF} F.canonicalTopologicalData (t + 1))

/-- Actual standard-module and twisted-block polynomial certificates with a
normalized residual whose triviality is the remaining product obligation. -/
structure LanglandsTypeLPolynomialData where
  inducedPolynomial : ℂ[X]
  blockPolynomial : Fin d.shape.length → Fin e.shape.length → ℂ[X]
  left_type : letI := F.canonicalTopologicalData.topology;
    IsOfWhittakerType r (standardCharacter ψ r) d.standardModule.representation
  right_type : letI := F.canonicalTopologicalData.topology;
    IsOfWhittakerType t (standardCharacter ψ t) e.standardModule.representation
  induced_spec : letI := F.canonicalTopologicalData.topology;
    IsPadicSymmetricLPolynomial F ψ ν.val
    d.standardModule.representation e.standardModule.representation inducedPolynomial
  block_spec : letI := F.canonicalTopologicalData.topology;
    ∀ i j, IsPadicRankLPolynomial F ψ ν.val
    (F.canonicalTopologicalData.twistedBlocks d.shape d.blocks d.exponent i).representation
    (F.canonicalTopologicalData.twistedBlocks e.shape e.blocks e.exponent j).representation
    (blockPolynomial i j)
  quotient : TemperedLFactorAlgebra.NormalizedPolynomialQuotient
    inducedPolynomial (∏ i, ∏ j, blockPolynomial i j)

/-- Construct the complete existence and divisibility data for the original
standard modules, without any supplied Whittaker or polynomial hypothesis. -/
def langlandsTypeLPolynomialData : LanglandsTypeLPolynomialData F ψ ν d e :=
  Classical.choice <| by
    let := F.canonicalTopologicalData.topology
    have hdtype := langlandsStandardModuleWhittakerType F ψ d
    have hetype := langlandsStandardModuleWhittakerType F ψ e
    rcases d with ⟨⟨k, size, pos, total⟩, π, hiπ, htπ, s, hs⟩
    rcases e with ⟨⟨l, size', pos', total'⟩, σ, hiσ, htσ, z, hz⟩
    obtain ⟨m, rfl⟩ : ∃ m : Fin k → ℕ, size = fun i => m i + 1 :=
      ⟨fun i => size i - 1, funext fun i => (Nat.sub_add_cancel (pos i)).symm⟩
    obtain ⟨n, rfl⟩ : ∃ n : Fin l → ℕ, size' = fun j => n j + 1 :=
      ⟨fun j => size' j - 1, funext fun j => (Nat.sub_add_cancel (pos' j)).symm⟩
    let c := TemperedLFactorDivisibility.twoFamilyLPolynomialData F ψ ν
      m n total total'
      (fun i => (F.canonicalTopologicalData.segmentFactor (π i) (s i)).representation)
      (fun j => (F.canonicalTopologicalData.segmentFactor (σ j) (z j)).representation)
      (fun i => analyticTemperedRealTwistWhittakerType F ψ
        (π i).representation (hiπ i) (htπ i) (s i))
      (fun j => analyticTemperedRealTwistWhittakerType F ψ
        (σ j).representation (hiσ j) (htσ j) (z j))
    exact ⟨{
      inducedPolynomial := c.inducedPolynomial
      blockPolynomial := c.blockPolynomial
      left_type := hdtype
      right_type := hetype
      induced_spec := c.induced_spec
      block_spec := c.block_spec
      quotient := c.quotient }⟩

end Langlands.RankinSelberg
