import Langlands.BushnellKutzko.GLMaximalSimpleTypeSets
import Langlands.BushnellKutzko.SupercuspidalClassContainment
import Langlands.Correspondence.HenniartNumericalStatement

/-! # Supercuspidal classes containing conjugate maximal simple types are unramified twists

BK93 (6.2.3), last assertion, printed p. 204, transferred to the classes of
`Correspondence.SupercuspidalAutomorphicClass` and to `G`-conjugate pairs. Proposition
definition only.
-/

noncomputable section

namespace Langlands.BushnellKutzko

section Instances

/-! The canonical instances of the p-adic field, under names specific to this module. -/

local instance supercuspidalClassConjugateTypeTwistTopology {p : ℕ} [Fact p.Prime]
    (K : PadicField p) : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

local instance supercuspidalClassConjugateTypeTwistValuativeRel {p : ℕ} [Fact p.Prime]
    (K : PadicField p) : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel

local instance supercuspidalClassConjugateTypeTwistLocalField {p : ℕ} [Fact p.Prime]
    (K : PadicField p) : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField

/-- **A3.** Let `p` be a prime, `K : PadicField p` and `k : ℕ`. Let `x` be a pair of
`glMaximalSimpleTypesAt (k + 1) K t m` for some `t, m ≥ 1`, or of
`glMaximalLevelZeroSimpleTypes (k + 1) K`, and let `x'` be a pair that is
`GL_{k+1}(K)`-conjugate to `x`. If a supercuspidal class `π` contains `x` and a supercuspidal
class `π'` contains `x'`, then `π'` is the unramified twist of `π` by some `z : ℂˣ`. -/
def SupercuspidalClassConjugateTypeTwistStatement.{uK, uV, uT} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k : ℕ)
    (x x' : GLRepresentationPair.{uK, uT} (k + 1) K.Carrier),
    ((∃ t m : ℕ, 1 ≤ t ∧ 1 ≤ m ∧ x ∈ glMaximalSimpleTypesAt.{uK, uT} (k + 1) K.Carrier t m) ∨
      x ∈ glMaximalLevelZeroSimpleTypes.{uK, uT} (k + 1) K.Carrier) →
    AreConjugatePairs x.2.representation x'.2.representation →
    ∀ π π' : Correspondence.SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat,
      SupercuspidalClassContainsType K π x.2 → SupercuspidalClassContainsType K π' x'.2 →
        ∃ z : ℂˣ, Henniart.Numerical.supercuspidalUnramifiedTwist K k z π = π'

end Instances

end Langlands.BushnellKutzko
