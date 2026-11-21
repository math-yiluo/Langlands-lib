import Langlands.Correspondence.AutomorphicActualGamma
import Langlands.Correspondence.AutomorphicPairFactors
import Langlands.Representation.RankinSelberg.GenericLanglandsQuotientLFactorProof
import Langlands.Representation.RankinSelberg.SupercuspidalLFactorCharacterizationSupport
import Langlands.Representation.RankinSelberg.SupercuspidalUnequalRankLFactorReduction
import Langlands.Representation.RankinSelberg.UniformRankOneTwistProof

/-! # The standard Euler polynomial of a supercuspidal representation -/

noncomputable section

set_option autoImplicit false

universe u uV uW

namespace Langlands.BaseChange

open Correspondence GeneralLinear HarmonicAnalysis RankinSelberg Whittaker
open RankinSelberg.SupercuspidalLFactorCharacterization

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local instance supercuspidalEulerTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance supercuspidalEulerValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance supercuspidalEulerLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance supercuspidalEulerGroupTopology (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n
local instance supercuspidalEulerTopologicalGroup (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

/-- The actual standard Euler polynomial is one for a supercuspidal first factor
of rank greater than one and the trivial second factor of rank one. -/
def SupercuspidalStandardEulerPolynomialStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (r : ℕ), 0 < r →
    ∀ (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F), IsSelfDualMeasure F ψ ν →
    ∀ (A : AutomorphicObject.{u, uV} F r.succPNat) (B : AutomorphicObject.{u, uV} F 1),
      (letI := F.canonicalTopologicalData.topology; IsSupercuspidal A.obj.representation) →
      Nonempty ((rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)).Equiv B.obj.representation) →
      ∀ P : Polynomial ℂ,
        IsAutomorphicPairLPolynomial F ψ ν (automorphicClassOf F A) (automorphicClassOf F B) P → P = 1

set_option maxHeartbeats 1200000 in
/-- Compare the polynomial of the generic pair with the Langlands polynomial
and apply the supercuspidal unequal-rank formula to that pair. -/
theorem supercuspidalStandardEulerPolynomial : SupercuspidalStandardEulerPolynomialStatement.{u, uV} := by
  intro p _ F r hr ψ ν hν A B hA hB P hP
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨A₀, B₀, J, J', ha, hb, ⟨a⟩, ⟨b⟩, hPL⟩ := hP
  obtain ⟨eA⟩ := (automorphicClassOf_eq_iff F A₀ A).mp ha
  obtain ⟨eB⟩ := (automorphicClassOf_eq_iff F B₀ B).mp hb
  obtain ⟨e₁⟩ := hB
  let a' := a.trans eA
  let b' := e₁.trans (b.trans eB).symm
  have hJ := (GeneralLinear.isSupercuspidal_iff_of_equiv a').mpr hA
  have hJi := (Langlands.isIrreducible_iff_of_equiv a').mpr A.property.1
  have hJg := isGeneric_of_isSupercuspidal F ψ r J hJi hJ
  have hJ'g := (Whittaker.isGeneric_iff_of_equiv ψ 0 b').mp
    (UniformRankOneTwist.isGeneric_rankOneCharacter_one F ψ)
  have hJ'wt := isOfWhittakerType_of_isGeneric F hJ'g
  have hP' := hPL.isPadicSymmetricLPolynomial (ν := ⟨ν, hν⟩) hJg hJ'g
  have hone := supercuspidalUnequalRankLFactor p F ψ ⟨ν, hν⟩ r 0
    J.representation J'.representation hJi hJ hJ'wt hr
  exact hP'.unique ((isPadicSymmetricLPolynomial_of_le (Nat.zero_le r)).mpr hone)

end Langlands.BaseChange
