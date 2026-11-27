import Langlands.BushnellKutzko.GLMaximalSimpleTypeSets
import Langlands.BushnellKutzko.SupercuspidalClassContainment

/-! # Every supercuspidal class of `GL_{k+1}` over a p-adic field contains a maximal simple type

BK93 (8.4.1), printed p. 297, with (6.2.1), printed p. 202, transferred to the classes of
`Correspondence.SupercuspidalAutomorphicClass`. Proposition definition only.
-/

noncomputable section

namespace Langlands.BushnellKutzko

section Instances

/-! The canonical instances of the p-adic field, under names specific to this module. -/

local instance supercuspidalClassMaximalTypeTopology {p : ℕ} [Fact p.Prime]
    (K : PadicField p) : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

local instance supercuspidalClassMaximalTypeValuativeRel {p : ℕ} [Fact p.Prime]
    (K : PadicField p) : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel

local instance supercuspidalClassMaximalTypeLocalField {p : ℕ} [Fact p.Prime]
    (K : PadicField p) : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField

/-- **A1.** For every prime `p`, every `K : PadicField p`, every `k : ℕ` and every supercuspidal
class `π` of `GL_{k+1}(K)`, `π` contains a pair of `glMaximalSimpleTypesAt (k + 1) K t m` for
some `t ≥ 1` dividing `k + 1` and some `m ≥ 1`, or a pair of
`glMaximalLevelZeroSimpleTypes (k + 1) K`. The pairs have carriers in the universe `uT`. -/
def SupercuspidalClassMaximalTypeStatement.{uK, uV, uT} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k : ℕ)
    (π : Correspondence.SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat),
    (∃ t m : ℕ, 1 ≤ t ∧ t ∣ k + 1 ∧ 1 ≤ m ∧
      ∃ x ∈ glMaximalSimpleTypesAt.{uK, uT} (k + 1) K.Carrier t m,
        SupercuspidalClassContainsType K π x.2) ∨
    ∃ x ∈ glMaximalLevelZeroSimpleTypes.{uK, uT} (k + 1) K.Carrier,
      SupercuspidalClassContainsType K π x.2

end Instances

end Langlands.BushnellKutzko
