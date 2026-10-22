import Langlands.Correspondence.FullFactorCompatibility
import Langlands.Correspondence.SupercuspidalGammaCompatibility

/-!
# Derived gamma compatibility of full families

The representation-side gamma factor of a pair of irreducible admissible classes is
`ε(s, π × π', ψ) L(1 - s, π^∨ × π'^∨) / L(s, π × π')`, built from the pair epsilon
and L relations defined through the Langlands classification and the published
explicit gamma expression. The parameter side is the published arithmetic gamma
relation. The derivation from the L, epsilon and dual conditions is stated as a
proposition only.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

open LocalFactor LocalFactor.CommonClosure Polynomial

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- `γ(s, π × π', ψ) = G(q^(-s))` for classes of ranks `r + 1` and `t + 1`: for some
contragredient classes `π^∨`, `π'^∨`, L-polynomials `P` of `(π, π')` and `P^∨` of
`(π^∨, π'^∨)`, and epsilon factor `c q^(-ms)` of `(π, π')`, all at `ψ` and `ν`,
`G` is `c X^m P(X) / P^∨(q⁻¹/X)`. -/
def IsAutomorphicPairGammaFactor (ψ : NontrivialAdditiveCharacter F)
    (ν : LocalAdditiveHaarMeasure F) {r t : ℕ}
    (π : AutomorphicClass.{uF, uA} F r.succPNat) (π' : AutomorphicClass.{uF, uA} F t.succPNat)
    (G : RatFunc ℂ) : Prop :=
  ∃ (πd : AutomorphicClass.{uF, uA} F r.succPNat) (πd' : AutomorphicClass.{uF, uA} F t.succPNat)
    (P Pd : ℂ[X]) (e : ℂˣ × ℤ),
    IsSmoothDual F π πd ∧ IsSmoothDual F π' πd' ∧
      IsAutomorphicPairLPolynomial F ψ ν π π' P ∧
      IsAutomorphicPairLPolynomial F ψ ν πd πd' Pd ∧
      IsAutomorphicPairEpsilonFactor F ψ ν π π' e ∧
      G = RankinSelberg.rationalGammaExpression (residueReflection F) e.1 e.2 P Pd

/-- Pair gamma compatibility of a full map for the supplied system: for every
nontrivial `ψ`, all ranks `r + 1`, `t + 1` and all parameter classes `D`, `D'`, a
self-dual measure exists, and for every self-dual measure some `G` is both the
gamma factor of the image pair and the arithmetic gamma factor of `D ⊗ D'`. -/
def FullPairGammaCompatibility (eC : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uP} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (c : FullMap.{uF, uP, uA} F) : Prop :=
  ∀ (ψ : NontrivialAdditiveCharacter F) (r t : ℕ)
    (D : WeilDeligneClass.{uF, uP} F r.succPNat) (D' : WeilDeligneClass.{uF, uP} F t.succPNat),
    (∃ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν) ∧
    ∀ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν →
      ∃ G : RatFunc ℂ,
        IsAutomorphicPairGammaFactor F ψ ν (c r.succPNat D) (c t.succPNat D') G ∧
          IsArithmeticPairGammaFactor F eC ε hε ψ (parameterForget F D) (parameterForget F D') G

/-- Gamma compatibility relative to a rank-one reciprocity candidate: some system
with base reciprocity component `e` satisfies `FullPairGammaCompatibility`. -/
def FullGammaCompatibility (e : ReciprocityCandidate F) (c : FullMap.{uF, uP, uA} F) :
    Prop :=
  ∃ (eC : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uP} F)
    (hε : NonabelianSystem.IsSystem F eC ε),
    IsBaseReciprocity F e eC ∧ FullPairGammaCompatibility F eC ε hε c

/-- Derived gamma compatibility (statement only): for every system and every full
map, pair L-factor compatibility, pair epsilon-factor compatibility for the system
and dual compatibility imply pair gamma compatibility for the same system and the
same map. -/
def FullGammaFromFactorsStatement : Prop :=
  ∀ (eC : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uP} F)
    (hε : NonabelianSystem.IsSystem F eC ε) (c : FullMap.{uF, uP, uA} F),
    FullPairLCompatibility F c → FullPairEpsilonCompatibility F eC ε hε c →
      DualCompatibility F c → FullPairGammaCompatibility F eC ε hε c

end Langlands.Correspondence
