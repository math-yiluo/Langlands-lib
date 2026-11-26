import Langlands.BaseChange.HighlyRamifiedStandardFactors
import Langlands.BaseChange.CompletionRelativeFieldInvariants
import Langlands.Automorphic.AssociatedGammaFinal
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Global.Factors.CuspidalPairPartialGammaReduction
import Langlands.Representation.Twist.AlgebraProof

/-! # Standard factor choices for determinant twists at finite completions -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.BaseChange

open Automorphic Correspondence GeneralLinear Global Global.CompletionPadic
open Global.CuspidalPairFunctionalEquation Global.HeckeFunctionalEquation
open ClassFieldTheory.Global.RelativeWeilGroup
open HarmonicAnalysis RankinSelberg Whittaker
open scoped NumberField

universe u uQ

section Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) {r : ℕ}
  (ψ : NontrivialAdditiveCharacter F) (A : AutomorphicObject.{u, u} F r.succPNat)
  (χ : QuasiCharacter F)

local instance standardTwistFieldTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology

/-- Certified standard factors of an actual determinant twist, with a trivial
rank-one partner and the self-dual measure for the supplied character. -/
structure StandardTwistFactorChoice where
  twisted : AutomorphicObject.{u, u} F r.succPNat
  rankOne : AutomorphicObject.{u, u} F 1
  twistEquiv : Nonempty ((twist (determinantQuasiCharacter F r.succPNat χ)
    A.obj.representation).Equiv twisted.obj.representation)
  trivialEquiv : Nonempty ((rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)).Equiv rankOne.obj.representation)
  measure : LocalAdditiveHaarMeasure F
  measure_spec : IsSelfDualMeasure F ψ measure
  lPolynomial : Polynomial ℂ
  epsilon : ℂˣ × ℤ
  lPolynomial_spec : IsAutomorphicPairLPolynomial F ψ measure
    (automorphicClassOf F twisted) (automorphicClassOf F rankOne) lPolynomial
  epsilon_spec : IsAutomorphicPairEpsilonFactor F ψ measure
    (automorphicClassOf F twisted) (automorphicClassOf F rankOne) epsilon

set_option maxHeartbeats 1000000 in
/-- The local bound applies to all class-level standard factor choices of the twist. -/
theorem exists_conductorBound_standardTwistFactors (hA : IsGeneric ψ r A.obj.representation) :
    ∃ B : ℕ, ∀ χ : QuasiCharacter F, B ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
      ∀ c : StandardTwistFactorChoice F ψ A χ,
        c.lPolynomial = 1 ∧ c.epsilon.2 = (r + 1 : ℕ) *
          LocalFactor.PadicAbelian.epsilonExponent F.canonicalTopologicalData χ ψ := by
  obtain ⟨B, hB⟩ := highlyRamifiedStandardFactors.{u, u} p F ψ r A.obj A.obj.representation hA
  refine ⟨B, fun η hη c => ?_⟩
  obtain ⟨e⟩ := c.twistEquiv
  obtain ⟨f⟩ := c.trivialEquiv
  let ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ := ⟨c.measure, c.measure_spec⟩
  have hG := (isGeneric_iff_of_equiv ψ r e).mp (UniformRankOneTwist.isGeneric_twist F ψ _ hA η)
  have h₁ := (isGeneric_iff_of_equiv ψ 0 f).mp (UniformRankOneTwist.isGeneric_rankOneCharacter_one F ψ)
  have hP := (isAutomorphicPairLPolynomial_iff F c.twisted c.rankOne c.twisted.obj c.rankOne.obj
    (Representation.Equiv.refl _) (Representation.Equiv.refl _)).mp c.lPolynomial_spec
  have hE := (isAutomorphicPairEpsilonFactor_iff F c.twisted c.rankOne c.twisted.obj c.rankOne.obj
    (Representation.Equiv.refl _) (Representation.Equiv.refl _)).mp c.epsilon_spec
  exact ⟨(hB η hη ν).1 c.lPolynomial
      ((IsPadicSymmetricLPolynomial.congr_equiv e f).mpr (hP.isPadicSymmetricLPolynomial (ν := ν) hG h₁)),
    (hB η hη ν).2 c.epsilon ((IsPadicSymmetricEpsilonFactor.congr_equiv e f).mpr
      (genericLanglandsPairEpsilonFactorComparison.{u, u, u} p F ψ ν r 0 c.twisted.obj c.rankOne.obj
        hG h₁ c.epsilon hE))⟩

end Local

local instance standardTwistRationalGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance standardTwistContinuousGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance standardTwistSmoothGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance standardTwistFormsGroup (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _

section Completion

variable {K : Type u} [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
  {r : ℕ} {T T' : CuspidalOperatorRealization K r} {T₁ : CuspidalOperatorRealization K 0}
  (D : CuspidalSpectralPresentation.{u, uQ} T) (D' : CuspidalSpectralPresentation.{u, uQ} T')
  (C : CuspidalSpectralPresentation.{u, uQ} T₁)
  (hD : HasIrreducibleAdmissibleComponents D) (hD' : HasIrreducibleAdmissibleComponents D')
  (hC : HasIrreducibleAdmissibleComponents C) (v : FinitePlace K)

local instance standardTwistAtCompletionLocalGroup {n : ℕ} (B : LocalRealization K n v) :
    AddCommGroup B.Space := Submodule.addCommGroup _

set_option maxHeartbeats 1000000 in
/-- Certify the actual completed local factors of a supplied global presentation from
its local twist equivalence and finite standard pair factor choices. -/
def standardTwistFactorChoiceAtCompletion (χ : QuasiCharacter (padicField v))
    (equiv : Nonempty ((twist (determinantQuasiCharacter (padicField v) r.succPNat χ)
      (D.localComponent v).representation).Equiv (D'.localComponent v).representation))
    (trivial : Nonempty ((rankOneCharacter (1 : (padicField v).Carrierˣ →* ℂˣ)).Equiv
      (C.localComponent v).representation))
    (ψ : NontrivialAdditiveCharacter (padicField v))
    (hψ : IsCanonicalFiniteAdditiveComponent (standardGlobalAdditiveCharacter K) v ψ)
    (ν : LocalAdditiveHaarMeasure (padicField v)) (hν : IsSelfDualMeasure (padicField v) ψ ν)
    (P : Polynomial ℂ) (b : ℂˣ × ℤ)
    (hP : IsAutomorphicPairLPolynomial (padicField v) ψ ν (localClass D' hD' v) (localClass C hC v) P)
    (hb : IsAutomorphicPairEpsilonFactor (padicField v) ψ ν (localClass D' hD' v) (localClass C hC v) b) :
    StandardTwistFactorChoice (padicField v) (standardFiniteAdditiveComponent K v)
      ((D.localComponent v).padicObject (hD v).1 (hD v).2) χ := by
  have hψeq := isCanonicalFiniteAdditiveComponent_unique hψ
    (isCanonicalFiniteAdditiveComponent_standardFiniteAdditiveComponent K v)
  refine ⟨(D'.localComponent v).padicObject (hD' v).1 (hD' v).2,
    (C.localComponent v).padicObject (hC v).1 (hC v).2, equiv, trivial, ν, hψeq ▸ hν,
    P, b, hψeq ▸ hP, hψeq ▸ hb⟩

end Completion

section PairChoices

variable {K : Type u} [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
  {r : ℕ} {T T' Td' : CuspidalOperatorRealization K r} {T₁ : CuspidalOperatorRealization K 0}
  (D : CuspidalSpectralPresentation.{u, uQ} T) (D' : CuspidalSpectralPresentation.{u, uQ} T')
  (Dd' : CuspidalSpectralPresentation.{u, uQ} Td') (C : CuspidalSpectralPresentation.{u, uQ} T₁)
  (hD : HasIrreducibleAdmissibleComponents D) (hD' : HasIrreducibleAdmissibleComponents D')
  (hDd' : HasIrreducibleAdmissibleComponents Dd') (hC : HasIrreducibleAdmissibleComponents C)
  (c : FinitePairFactorChoice (standardGlobalAdditiveCharacter K) D' C Dd' C hD' hC hDd' hC)
  (v : FinitePlace K) (χ : QuasiCharacter (padicField v))

local instance standardPairChoiceLocalGroup {n : ℕ} (B : LocalRealization K n v) :
    AddCommGroup B.Space := Submodule.addCommGroup _

/-- The forward polynomial and epsilon factor give the local standard choice. -/
def forwardStandardTwistFactorChoice
    (equiv : Nonempty ((twist (determinantQuasiCharacter (padicField v) r.succPNat χ)
      (D.localComponent v).representation).Equiv (D'.localComponent v).representation))
    (trivial : Nonempty ((rankOneCharacter (1 : (padicField v).Carrierˣ →* ℂˣ)).Equiv
      (C.localComponent v).representation)) :
    StandardTwistFactorChoice (padicField v) (standardFiniteAdditiveComponent K v)
      ((D.localComponent v).padicObject (hD v).1 (hD v).2) χ :=
  standardTwistFactorChoiceAtCompletion D D' C hD hD' hC v χ equiv trivial (c.additive v)
    (c.additive_spec v) (c.measure v) (c.measure_spec v) (c.lPolynomial v) (c.epsilon v)
    (c.lPolynomial_spec v) (c.epsilon_spec v)

/-- The dual polynomial gives the local standard choice for the dual pair,
with an epsilon factor chosen at the same character and measure. -/
def dualStandardTwistFactorChoice
    (equiv : Nonempty ((twist (determinantQuasiCharacter (padicField v) r.succPNat χ)
      (D.localComponent v).representation).Equiv (Dd'.localComponent v).representation))
    (trivial : Nonempty ((rankOneCharacter (1 : (padicField v).Carrierˣ →* ℂˣ)).Equiv
      (C.localComponent v).representation)) :
    StandardTwistFactorChoice (padicField v) (standardFiniteAdditiveComponent K v)
      ((D.localComponent v).padicObject (hD v).1 (hD v).2) χ :=
  let he := exists_isAutomorphicPairEpsilonFactor (padicField v) (c.additive v) (c.measure_spec v)
    (localClass Dd' hDd' v) (localClass C hC v)
  standardTwistFactorChoiceAtCompletion D Dd' C hD hDd' hC v χ equiv trivial (c.additive v)
    (c.additive_spec v) (c.measure v) (c.measure_spec v) (c.dualLPolynomial v) he.choose
    (c.dualLPolynomial_spec v) he.choose_spec

end PairChoices

end Langlands.BaseChange
