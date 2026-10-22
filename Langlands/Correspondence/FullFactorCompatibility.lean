import Langlands.Correspondence.FullLFactorCompatibility
import Langlands.Representation.RankinSelberg.LanglandsFactors

/-!
# Pair L- and epsilon-factor compatibility of full families

The representation side of the epsilon clause is the pair epsilon factor of
irreducible admissible representations defined through the Langlands
classification, on representatives of automorphic classes. The parameter side is
the arithmetic epsilon factor of the underlying Weil–Deligne pair classes for a
supplied local-constant system. The full condition conjoins it with the L-clause
of `FullLFactorCompatibility`, for every nontrivial `ψ` or at one `ψ`. No additive
character, measure or system is chosen.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

open LocalFactor LocalFactor.CommonClosure

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance fullFactorFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance fullFactorGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- `ε(s, π × π', ψ) = c q^(-ms)`, `e = (c, m)`, for classes of ranks `r + 1` and
`t + 1`: some representatives are equivalent to representations `J`, `J'` with
carriers in `max uF uA` that satisfy the pair epsilon relation defined through the
Langlands classification. -/
def IsAutomorphicPairEpsilonFactor (ψ : NontrivialAdditiveCharacter F)
    (ν : LocalAdditiveHaarMeasure F) {r t : ℕ}
    (π : AutomorphicClass.{uF, uA} F r.succPNat) (π' : AutomorphicClass.{uF, uA} F t.succPNat)
    (e : ℂˣ × ℤ) : Prop :=
  ∃ (A : AutomorphicObject.{uF, uA} F r.succPNat) (A' : AutomorphicObject.{uF, uA} F t.succPNat)
    (J : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (r + 1) F.Carrier))
    (J' : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (t + 1) F.Carrier)),
    automorphicClassOf F A = π ∧ automorphicClassOf F A' = π' ∧
      Nonempty (J.representation.Equiv A.obj.representation) ∧
      Nonempty (J'.representation.Equiv A'.obj.representation) ∧
      RankinSelberg.IsLanglandsPairEpsilonFactor.{uF, uA, uA} F ψ ν J J' e

/-- `ε(s, π × π', ψ) = ε(s, D ⊗ D', ψ)` for the supplied system: a self-dual
measure for `ψ` exists, and for every such measure `ν` some `c q^(-ms)` is both the
epsilon factor of `(π, π')` and the arithmetic epsilon factor of `D ⊗ D'`. -/
def IsPairEpsilonCompatibleAt (eC : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uP} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (ψ : NontrivialAdditiveCharacter F) {r t : ℕ}
    (D : WeilDeligneClass.{uF, uP} F r.succPNat) (D' : WeilDeligneClass.{uF, uP} F t.succPNat)
    (π : AutomorphicClass.{uF, uA} F r.succPNat) (π' : AutomorphicClass.{uF, uA} F t.succPNat) :
    Prop :=
  (∃ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν) ∧
    ∀ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν →
      ∃ e : ℂˣ × ℤ, IsAutomorphicPairEpsilonFactor F ψ ν π π' e ∧
        IsArithmeticPairEpsilonFactor F eC ε hε ψ (parameterForget F D) (parameterForget F D')
          e.1 e.2

/-- Pair epsilon-factor compatibility of a full map at one nontrivial `ψ` for the
supplied system, for all ranks `r + 1`, `t + 1` and all parameter classes. -/
def FullPairEpsilonCompatibilityAt (eC : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uP} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (ψ : NontrivialAdditiveCharacter F) (c : FullMap.{uF, uP, uA} F) : Prop :=
  ∀ (r t : ℕ) (D : WeilDeligneClass.{uF, uP} F r.succPNat)
    (D' : WeilDeligneClass.{uF, uP} F t.succPNat),
    IsPairEpsilonCompatibleAt F eC ε hε ψ D D' (c r.succPNat D) (c t.succPNat D')

/-- Pair epsilon-factor compatibility of a full map for the supplied system and
every nontrivial `ψ`. -/
def FullPairEpsilonCompatibility (eC : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uP} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (c : FullMap.{uF, uP, uA} F) : Prop :=
  ∀ ψ : NontrivialAdditiveCharacter F, FullPairEpsilonCompatibilityAt F eC ε hε ψ c

/-- Epsilon compatibility relative to a rank-one reciprocity candidate: some
local-constant system whose reciprocity family has `e` as its base component
satisfies `FullPairEpsilonCompatibility`. -/
def FullEpsilonCompatibility (e : ReciprocityCandidate F) (c : FullMap.{uF, uP, uA} F) :
    Prop :=
  ∃ (eC : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uP} F)
    (hε : NonabelianSystem.IsSystem F eC ε),
    IsBaseReciprocity F e eC ∧ FullPairEpsilonCompatibility F eC ε hε c

/-- The full pair-factor condition relative to `e`: L-factor compatibility and
epsilon-factor compatibility, both for every nontrivial `ψ`. -/
def FullFactorCompatibility (e : ReciprocityCandidate F) (c : FullMap.{uF, uP, uA} F) :
    Prop :=
  FullPairLCompatibility F c ∧ FullEpsilonCompatibility F e c

/-- The full pair-factor condition relative to `e` at one nontrivial `ψ`: L-factor
compatibility at `ψ`, and some system with base component `e` gives epsilon-factor
compatibility at `ψ`. -/
def FullFactorCompatibilityAt (e : ReciprocityCandidate F) (ψ : NontrivialAdditiveCharacter F)
    (c : FullMap.{uF, uP, uA} F) : Prop :=
  FullPairLCompatibilityAt F ψ c ∧
    ∃ (eC : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uP} F)
      (hε : NonabelianSystem.IsSystem F eC ε),
      IsBaseReciprocity F e eC ∧ FullPairEpsilonCompatibilityAt F eC ε hε ψ c

end Langlands.Correspondence
