import Langlands.BaseChange.SupercuspidalStandardFactorsAtCompletion
import Langlands.LocalField.PadicBridge
import Langlands.Representation.Conductor.SphericalCorankOneRankOneGamma
import Langlands.Representation.RankinSelberg.AdjacentRankLargeTwistLDivisibility
import Langlands.Representation.RankinSelberg.HighlyRamified.Duality
import Langlands.Representation.RankinSelberg.HighlyRamified.ShellDischarge

/-! # The distinguished standard Euler polynomials and their duals -/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.BaseChange

open Automorphic Correspondence Global Global.CompletionPadic
open Global.CuspidalPairFunctionalEquation
open GeneralLinear RankinSelberg Whittaker HarmonicAnalysis MeasureTheory
open scoped PadicField.CanonicalLocalField

section Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) {r : ℕ}
  (A : AutomorphicObject.{u, u} F r.succPNat)
  (B : AutomorphicObject.{u, u} F 1)
  (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F)

local instance distinguishedEulerTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology

private theorem generic_of_standardEpsilon (hr : 0 < r) (e : ℂˣ × ℤ)
    (h : IsPadicPairEpsilonFactor F ψ ν A.obj.representation (rankOneCharacter 1) e) :
    IsGeneric ψ r A.obj.representation := by
  let := borel (GeneralLinear 1 F.Carrier)
  let : BorelSpace (GeneralLinear 1 F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent 1 F.Carrier)
  let : BorelSpace (upperUnipotent 1 F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient 0 F.Carrier)
  change IsPairEpsilonFactor F.canonicalTopologicalData.residueCardinality ψ
    (RankinSelberg.normalizedAbsoluteValue F.canonicalTopologicalData) ν
    A.obj.representation (rankOneCharacter 1) e at h
  exact ⟨A.property.1, A.property.2, ((isPairEpsilonFactor_of_lt hr).mp h).2.1⟩

/-- On an actual generic standard pair, the Langlands polynomial used in a
completed equation is the JPSS polynomial of the same pair. -/
theorem automorphicStandardLPolynomial_eq_of_localCertificate
    (hν : IsSelfDualMeasure F ψ ν)
    (hA : IsGeneric ψ r A.obj.representation)
    (b : (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)).Equiv B.obj.representation)
    {P P₀ : Polynomial ℂ}
    (hP : IsAutomorphicPairLPolynomial F ψ ν (automorphicClassOf F A) (automorphicClassOf F B) P)
    (hP₀ : IsPadicPairLPolynomial F ψ ν A.obj.representation (rankOneCharacter 1) P₀) :
    P = P₀ := by
  have hB := (isGeneric_iff_of_equiv ψ 0 b).mp (UniformRankOneTwist.isGeneric_rankOneCharacter_one F ψ)
  have hPL := (isAutomorphicPairLPolynomial_iff F A B A.obj B.obj
    (Representation.Equiv.refl _) (Representation.Equiv.refl _)).mp hP
  have hP' := hPL.isPadicSymmetricLPolynomial (ν := ⟨ν, hν⟩) hA hB
  have hP₀' := (IsPadicPairLPolynomial.congr_equiv (Representation.Equiv.refl _) b).mp hP₀
  exact ((isPadicSymmetricLPolynomial_of_le (Nat.zero_le r)).mp hP').unique hP₀'

end Local

/-- The standard forward and dual polynomials of a completed pair equal the
supplied local JPSS polynomials at the completion. The actual local epsilon
certificate supplies genericity of the first component. -/
def DistinguishedStandardEulerPolynomialsStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ), 0 < r →
    ∀ (T Td : CuspidalOperatorRealization K r), Td.realization.IsContragredientOf T.realization →
    ∀ (P : CuspidalSpectralPresentation.{u, uQ} T) (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
      (hP : HasIrreducibleAdmissibleComponents P) (hPd : HasIrreducibleAdmissibleComponents Pd)
      (Ψ : UnitaryAdditiveCharacter (Adeles K)),
    let C := ConstantFunctions.rankOneSpectralPresentation.{u, uQ} K
    let hC := ConstantFunctions.rankOneSpectralPresentation_hasIrreducibleAdmissibleComponents.{u, uQ} K
    ∀ (c : FinitePairFactorChoice Ψ P C Pd C hP hC hPd hC) (w : FinitePlace K),
    let F := padicField w
    letI : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
    letI : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
    letI : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
    letI (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopology n
    let A := (P.localComponent w).padicObject (hP w).1 (hP w).2
    let one := rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)
    ∀ (e : ℂˣ × ℤ) (p₀ pd₀ : Polynomial ℂ),
      IsPadicPairEpsilonFactor F (c.additive w) (c.measure w) A.obj.representation one e →
      IsPadicPairLPolynomial F (c.additive w) (c.measure w) A.obj.representation one p₀ →
      IsPadicPairLPolynomial F ((c.additive w).scale (-1)) (c.measure w)
        (inverseTransposePullback A.obj.representation) (inverseTransposePullback one) pd₀ →
      c.lPolynomial w = p₀ ∧ c.dualLPolynomial w = pd₀

set_option maxHeartbeats 2500000 in
theorem distinguishedStandardEulerPolynomials : DistinguishedStandardEulerPolynomialsStatement.{u, uQ} := by
  intro K _ _ _ r hr T Td ht P Pd hP hPd Ψ C hC c w F A one e p₀ pd₀ he hp hd
  let : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
  let : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
  let : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
  let (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopology n
  let (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopologicalGroup n
  let Ad := (Pd.localComponent w).padicObject (hPd w).1 (hPd w).2
  let B := (C.localComponent w).padicObject (hC w).1 (hC w).2
  let ψ := c.additive w
  let ν := c.measure w
  obtain ⟨b⟩ := ConstantFunctions.rankOneSpectralPresentation_localTrivialEquiv.{u, uQ} K w
  have ha := generic_of_standardEpsilon F A ψ ν hr e he
  have had := HighlyRamified.isGeneric_of_scale_neg_one ψ
    (HighlyRamified.isGeneric_inverseTransposePullback F ψ A.obj.representation ha)
  obtain ⟨d⟩ := cuspidalContragredientLocalCompatibility K r T Td ht P Pd w
    (hP w).1 (hP w).2 (hPd w).1 (hPd w).2
  let d' := (inverseTransposeSmoothDualEquiv F A.obj.representation A.property.2 A.property.1).trans d.symm
  have hg := (isGeneric_iff_of_equiv ψ r d').mp had
  have hc := (RankinSelberg.Padic.isPadicPairLPolynomial_characterChange F ψ (-1) ν
      (inverseTransposePullback A.obj.representation) (inverseTransposePullback one) pd₀).mpr hd
  rw [Langlands.Conductor.SphericalCorankOne.inverseTransposePullback_rankOneCharacter_one] at hc
  have hc' := (IsPadicPairLPolynomial.congr_equiv d' (Representation.Equiv.refl one)).mp hc
  exact ⟨automorphicStandardLPolynomial_eq_of_localCertificate F A B ψ ν (c.measure_spec w)
      ha b (c.lPolynomial_spec w) hp,
    automorphicStandardLPolynomial_eq_of_localCertificate F Ad B ψ ν (c.measure_spec w)
      hg b (c.dualLPolynomial_spec w) hc'⟩

end Langlands.BaseChange
