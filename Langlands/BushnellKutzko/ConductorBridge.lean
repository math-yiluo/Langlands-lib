import Langlands.Representation.RankinSelberg.AdjacentRankGammaData
import Langlands.Representation.RankinSelberg.RankOneAmbientMatrixFunctionalEquationComparisonProof
import Langlands.Representation.GodementJacquet.SubquotientCoefficientInclusionProof
import Langlands.Representation.RankinSelberg.SymmetricGammaExpressionProof
import Langlands.Representation.RankinSelberg.PadicGenericGammaFactor
import Langlands.Representation.RankinSelberg.SupercuspidalUnequalRankLFactorReduction
import Langlands.Representation.RankinSelberg.SupercuspidalLFactorCharacterizationSupport
import Langlands.Representation.RankinSelberg.UniformRankOneTwistProof
import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualDuality
import Langlands.Representation.RankinSelberg.DualWhittakerType
import Langlands.Representation.Classification.SupercuspidalInverseTranspose
import Langlands.Representation.Classification.SupercuspidalStrata
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Representation.Conductor.SupercuspidalPadicGenericConductor
import Langlands.Representation.Conductor.SupercuspidalPadicConductorExponentProof

/-! # The functional-equation exponent is the conductor (bridge B)

Let `K` be a `p`-adic field, `ψ` an additive character of conductor `𝔬_K`, `ν` self-dual for
`ψ`, and `A` an irreducible supercuspidal representation of `GL_{n+1}(K)` with `n ≥ 1`. If the
Godement–Jacquet functional equation of `A` has both Euler polynomials `1`, unit `c` and exponent
`a`, then `a` is a natural number `m` and the first fixed level of the class of `A` (the
conductor `Henniart.Numerical.conductor` of the target statement) is `m`
(`exists_exponent_eq_firstFixedLevel`).

Route: the Library comparison `rankOneAmbientMatrixFunctionalEquationComparison` turns the
functional equation into the Rankin–Selberg gamma factor `γ(s, A × 1, ψ) = c q^{-a s}`; the
Library theorem `symmetricGammaExpression` with `L(s, A × 1) = 1` and its dual
(`supercuspidalUnequalRankLFactor`) gives `γ(s, A × 1, ψ) = ε(s, A × 1, ψ)`; and the Library
conductor theorem for supercuspidals (`genericConductor_isNewvectorConductor_of_supercuspidalPadic`
with `supercuspidalPadicConductorExponent`) identifies the exponent of `ε(s, A × 1, ψ)` with the
newvector level.
-/

noncomputable section

open MeasureTheory Langlands.HarmonicAnalysis

namespace Langlands.BushnellKutzko

universe uK uV

section Padic

local instance brTopologicalSpace {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance brValuativeRel {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel

local instance brLocalField {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

local instance brT2 {p : ℕ} [Fact p.Prime] (F : PadicField p) : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2

local instance brDisconnected {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local instance brMeasurable {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    MeasurableSpace F.Carrier :=
  borel _

local instance brBorel {p : ℕ} [Fact p.Prime] (F : PadicField p) : BorelSpace F.Carrier :=
  ⟨rfl⟩

set_option maxHeartbeats 800000

attribute [local irreducible] GodementJacquet.biSmoothMatrixCoefficients
  Whittaker.coefficientModel Whittaker.modelRepresentation

/-- Two rational gamma expressions with trivial polynomials have the same exponent. -/
theorem exponent_eq_of_rationalGammaExpression_eq {δ c c' : ℂˣ} {a m : ℤ}
    (h : RankinSelberg.rationalGammaExpression δ c a 1 1 =
      RankinSelberg.rationalGammaExpression δ c' m 1 1) :
    a = m := by
  simp only [RankinSelberg.rationalGammaExpression, map_one, mul_one, div_one] at h
  have h1 := congrArg (RatFunc.eval (RingHom.id ℂ) 1) h
  have h2 := congrArg (RatFunc.eval (RingHom.id ℂ) 2) h
  rw [RankinSelberg.eval_rationalEpsilonMonomial c a one_ne_zero,
    RankinSelberg.eval_rationalEpsilonMonomial c' m one_ne_zero] at h1
  rw [RankinSelberg.eval_rationalEpsilonMonomial c a two_ne_zero,
    RankinSelberg.eval_rationalEpsilonMonomial c' m two_ne_zero] at h2
  simp only [one_zpow, mul_one] at h1
  rw [h1] at h2
  have h3 : (2 : ℂ) ^ a = (2 : ℂ) ^ m := mul_left_cancel₀ c'.ne_zero h2
  have h4 : (2 : ℝ) ^ a = (2 : ℝ) ^ m := by
    apply Complex.ofReal_injective
    push_cast
    exact h3
  exact zpow_right_injective₀ (by norm_num) (by norm_num) h4

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- Godement–Jacquet functional-equation data of a representation of Whittaker type give its
Rankin–Selberg gamma factor against the trivial character of `GL_1`. This is the argument of
the Library lemma `gammaData_rankOne_of_matrix` (module
`RankinSelberg.AdjacentRankGammaData`) with `ρ = σ`. -/
theorem isPadicSymmetricGammaFactor_of_matrixFunctionalEquationData
    (ψ : UnitaryAdditiveCharacter K.Carrier) (ν : AdditiveHaarMeasure K.Carrier)
    (hsd : IsSelfDual ψ ν) {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (n + 1) K.Carrier) V)
    (hσ : RankinSelberg.IsOfWhittakerType n (Whittaker.standardCharacter ψ n) σ)
    (P PDual : Polynomial ℂ) (c : ℂˣ) (a : ℤ)
    (hFE : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData K ψ ν σ P PDual c a) :
    RankinSelberg.IsPadicSymmetricGammaFactor K ψ ν σ
      (RankinSelberg.rankOneCharacter (1 : K.Carrierˣ →* ℂˣ))
      (RankinSelberg.rationalGammaExpression (LocalFactor.residueReflection K) c a P PDual) :=
  RankinSelberg.Padic.gammaData_rankOne_of_matrix K ψ ν hsd σ hσ P PDual c a hFE

/-- **Bridge B.** Let `ψ` have conductor `𝔬_K`, `ν` be self-dual for `ψ`, `n ≥ 1`, and `A` an
irreducible supercuspidal representation of `GL_{n+1}(K)` whose Godement–Jacquet functional
equation has both Euler polynomials `1`, unit `c` and exponent `a`. Then `a = m` for a natural
number `m`, and the first fixed level of the class of `A` is `m`. -/
theorem exists_exponent_eq_firstFixedLevel
    (ψ : UnitaryAdditiveCharacter K.Carrier) (hψ : Conductor.HasIntegerConductor ψ)
    (ν : AdditiveHaarMeasure K.Carrier) (hsd : IsSelfDual ψ ν) {n : ℕ} (hn : 0 < n)
    (A : GeneralLinear.SupercuspidalRep.{uK, uV} (F := K.Carrier) (n := n + 1)) (c : ℂˣ)
    (a : ℤ)
    (hFE : GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData K ψ ν
      A.obj.representation 1 1 c a) :
    ∃ m : ℕ, a = m ∧ GeneralLinear.SupercuspidalClass.firstFixedLevel A.isoClass = m := by
  have hirr : A.obj.representation.IsIrreducible := A.property.1
  have hsc : GeneralLinear.IsSupercuspidal A.obj.representation := A.property.2
  have hgen : Whittaker.IsGeneric ψ n A.obj.representation :=
    RankinSelberg.SupercuspidalLFactorCharacterization.isGeneric_of_isSupercuspidal K ψ n A.obj
      hirr hsc
  have hW := RankinSelberg.isOfWhittakerType_of_isGeneric K hgen
  have h1gen := RankinSelberg.UniformRankOneTwist.isGeneric_rankOneCharacter_one K ψ
  have h1W := RankinSelberg.isOfWhittakerType_of_isGeneric K h1gen
  -- the gamma factor from the functional equation
  have hγ := isPadicSymmetricGammaFactor_of_matrixFunctionalEquationData K ψ ν hsd
    A.obj.representation hW 1 1 c a hFE
  -- the conductor and the epsilon factor
  obtain ⟨m, hm, hnew, -⟩ :=
    Conductor.genericConductor_isNewvectorConductor_of_supercuspidalPadic K
      Conductor.supercuspidalPadicConductorExponent ψ hψ A.obj.representation hgen hsc
  obtain ⟨c', hc'⟩ :=
    Conductor.exists_isPadicPairEpsilonFactor_genericConductor K ψ A.obj.representation hgen ν
      hsd
  rw [hm, Conductor.additiveConductor_eq_zero_of_hasIntegerConductor K ψ hψ, mul_zero,
    add_zero] at hc'
  have he : RankinSelberg.IsPadicSymmetricEpsilonFactor K ψ ν A.obj.representation
      (RankinSelberg.rankOneCharacter (1 : K.Carrierˣ →* ℂˣ)) (c', (m : ℤ)) :=
    (RankinSelberg.isPadicSymmetricEpsilonFactor_of_le (Nat.zero_le n)).mpr hc'
  -- the L-polynomials are trivial
  let ν' : LocalFactor.PadicAbelian.SelfDualHaar K.canonicalTopologicalData ψ := ⟨ν, hsd⟩
  have hP : RankinSelberg.IsPadicSymmetricLPolynomial K ψ ν A.obj.representation
      (RankinSelberg.rankOneCharacter (1 : K.Carrierˣ →* ℂˣ)) 1 :=
    (RankinSelberg.isPadicSymmetricLPolynomial_of_le (Nat.zero_le n)).mpr
      (RankinSelberg.supercuspidalUnequalRankLFactor p K ψ ν' n 0 A.obj.representation
        (RankinSelberg.rankOneCharacter (1 : K.Carrierˣ →* ℂˣ)) hirr hsc h1W hn)
  have hPd : RankinSelberg.IsPadicSymmetricLPolynomial K (ψ.scale (-1)) ν
      (Whittaker.inverseTransposePullback A.obj.representation)
      (Whittaker.inverseTransposePullback
        (RankinSelberg.rankOneCharacter (1 : K.Carrierˣ →* ℂˣ))) 1 := by
    have hscd : GeneralLinear.IsSupercuspidal
        (Whittaker.inverseTransposePullback A.obj.representation) :=
      GeneralLinear.isSupercuspidal_comp_inverseTranspose A.obj.representation hsc
    have hird : (Whittaker.inverseTransposePullback A.obj.representation).IsIrreducible :=
      (isIrreducible_comp_continuousMulEquiv_iff A.obj.representation
        (GeneralLinear.inverseTransposeContinuous (n + 1) K.Carrier)).mpr hirr
    have hWd : RankinSelberg.IsOfWhittakerType 0 (Whittaker.standardCharacter (ψ.scale (-1)) 0)
        (Whittaker.inverseTransposePullback
          (RankinSelberg.rankOneCharacter (1 : K.Carrierˣ →* ℂˣ))) := by
      rw [RankinSelberg.standardCharacter_scale_neg_one]
      exact RankinSelberg.isOfWhittakerType_inverseTransposePullback ψ _ h1W
    exact (RankinSelberg.isPadicSymmetricLPolynomial_of_le (Nat.zero_le n)).mpr
      (RankinSelberg.supercuspidalUnequalRankLFactor p K (ψ.scale (-1))
        (RankinSelberg.DominantRankTransport.negatedSelfDualHaar K ψ ν') n 0 _ _ hird hscd
        hWd hn)
  -- gamma is epsilon
  have hiff := RankinSelberg.symmetricGammaExpression p K ψ ν' n 0 A.obj.representation
    (RankinSelberg.rankOneCharacter (1 : K.Carrierˣ →* ℂˣ))
    (RankinSelberg.genericSymmetricGammaConstructionInput K ψ ν hsd A.obj.representation _
      hgen h1gen)
    (c', (m : ℤ)) 1 1 he hP hPd
    (RankinSelberg.rationalGammaExpression (LocalFactor.residueReflection K) c a 1 1)
  have ha := exponent_eq_of_rationalGammaExpression_eq (hiff.mp hγ)
  refine ⟨m, ha, ?_⟩
  rw [GeneralLinear.SupercuspidalClass.firstFixedLevel_isoClass]
  have hh : Conductor.HasNewvectorLevel A.obj.representation := ⟨m, hnew.1⟩
  rw [Conductor.firstFixedLevel_of_hasNewvectorLevel A.obj.representation hh,
    (Conductor.newvectorConductor_eq_iff A.obj.representation hh m).2 hnew]

end Padic

end Langlands.BushnellKutzko
