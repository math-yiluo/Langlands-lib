import Langlands.Correspondence.ArithmeticFactors
import Langlands.Representation.RankinSelberg.LanglandsQuotientLFactorStatement

/-!
# Pair L-factor compatibility of full families

The representation side is the published JPSS L-factor of pairs of irreducible
admissible representations, defined through the Langlands classification, on
representatives of automorphic classes. The parameter side is the arithmetic pair
L-factor of the underlying Weil–Deligne pair classes. No additive character or
measure is chosen. The epsilon clause is a separate condition.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

open Polynomial

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance fullLFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance fullLGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- `L(s, π × π') = 1 / P(q^(-s))` for classes of ranks `r + 1` and `t + 1`: some
representatives are equivalent to representations `J`, `J'` with carriers in
`max uF uA` that satisfy the published JPSS relation defined through the Langlands
classification. -/
def IsAutomorphicPairLPolynomial (ψ : NontrivialAdditiveCharacter F)
    (ν : LocalAdditiveHaarMeasure F) {r t : ℕ}
    (π : AutomorphicClass.{uF, uA} F r.succPNat) (π' : AutomorphicClass.{uF, uA} F t.succPNat)
    (P : ℂ[X]) : Prop :=
  ∃ (A : AutomorphicObject.{uF, uA} F r.succPNat) (A' : AutomorphicObject.{uF, uA} F t.succPNat)
    (J : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (r + 1) F.Carrier))
    (J' : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (t + 1) F.Carrier)),
    automorphicClassOf F A = π ∧ automorphicClassOf F A' = π' ∧
      Nonempty (J.representation.Equiv A.obj.representation) ∧
      Nonempty (J'.representation.Equiv A'.obj.representation) ∧
      RankinSelberg.IsLanglandsPairLPolynomial.{uF, uA, uA} F ψ ν J J' P

/-- `L(s, π × π') = L(s, D ⊗ D')` at `ψ`: a self-dual measure for `ψ` exists, and
for every such measure `ν` some `P` is the JPSS L-polynomial of `(π, π')` with
`1 / P(q^(-s))` the arithmetic L-factor of `D ⊗ D'`. -/
def IsPairLCompatibleAt (ψ : NontrivialAdditiveCharacter F) {r t : ℕ}
    (D : WeilDeligneClass.{uF, uP} F r.succPNat) (D' : WeilDeligneClass.{uF, uP} F t.succPNat)
    (π : AutomorphicClass.{uF, uA} F r.succPNat) (π' : AutomorphicClass.{uF, uA} F t.succPNat) :
    Prop :=
  (∃ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν) ∧
    ∀ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν →
      ∃ P : ℂ[X], IsAutomorphicPairLPolynomial F ψ ν π π' P ∧
        arithmeticPairLFactor F (parameterForget F D) (parameterForget F D') =
          (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹

/-- Pair L-factor compatibility of a full map at one nontrivial `ψ`, for all ranks
`r + 1`, `t + 1` and all parameter classes `D`, `D'`. -/
def FullPairLCompatibilityAt (ψ : NontrivialAdditiveCharacter F)
    (c : FullMap.{uF, uP, uA} F) : Prop :=
  ∀ (r t : ℕ) (D : WeilDeligneClass.{uF, uP} F r.succPNat)
    (D' : WeilDeligneClass.{uF, uP} F t.succPNat),
    IsPairLCompatibleAt F ψ D D' (c r.succPNat D) (c t.succPNat D')

/-- Pair L-factor compatibility of a full map for every nontrivial `ψ`. -/
def FullPairLCompatibility (c : FullMap.{uF, uP, uA} F) : Prop :=
  ∀ ψ : NontrivialAdditiveCharacter F, FullPairLCompatibilityAt F ψ c

end Langlands.Correspondence
