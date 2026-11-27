import Langlands.BushnellKutzko.GLMaximalSimpleTypeSets
import Langlands.BushnellKutzko.SupercuspidalClassContainment
import Langlands.Correspondence.HenniartRefinedStrata

/-! # Torsion number and Swan exponent of a supercuspidal class containing a maximal simple type

Torsion number: BK93 (6.2.5), printed pp. 204–205. Swan exponent: BK94 (3.10)(i), printed
p. 127, from Bushnell–Fröhlich (1985), (3.3.8), and Bushnell (1987), Theorem 3; with BK93
(2.3.2), printed p. 57. Transferred to the classes of
`Correspondence.SupercuspidalAutomorphicClass`. Proposition definition only.
-/

noncomputable section

namespace Langlands.BushnellKutzko

section Instances

/-! The canonical instances of the p-adic field, under names specific to this module. -/

local instance supercuspidalClassTypeInvariantsTopology {p : ℕ} [Fact p.Prime]
    (K : PadicField p) : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

local instance supercuspidalClassTypeInvariantsValuativeRel {p : ℕ} [Fact p.Prime]
    (K : PadicField p) : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel

local instance supercuspidalClassTypeInvariantsLocalField {p : ℕ} [Fact p.Prime]
    (K : PadicField p) : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField

/-- **A2.** Let `p` be a prime, `K : PadicField p`, `k : ℕ` and `π` a supercuspidal class of
`GL_{k+1}(K)`.
(a) If `π` contains a pair of `glMaximalSimpleTypesAt (k + 1) K t m` with `t ≥ 1` and `m ≥ 1`,
then `t ∣ k + 1`, the torsion number of `π` is `(k + 1) / t` and its Swan exponent is
`m * ((k + 1) / t)`.
(b) If `π` contains a pair of `glMaximalLevelZeroSimpleTypes (k + 1) K`, then the torsion
number of `π` is `k + 1` and its Swan exponent is `0`. -/
def SupercuspidalClassTypeInvariantsStatement.{uK, uV, uT} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k : ℕ)
    (π : Correspondence.SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat),
    (∀ t m : ℕ, 1 ≤ t → 1 ≤ m →
      ∀ x ∈ glMaximalSimpleTypesAt.{uK, uT} (k + 1) K.Carrier t m,
        SupercuspidalClassContainsType K π x.2 →
          t ∣ k + 1 ∧ Henniart.Numerical.supercuspidalTorsionNumber K π = (k + 1) / t ∧
            Henniart.Numerical.HasSupercuspidalSwan K π (m * ((k + 1) / t))) ∧
    ∀ x ∈ glMaximalLevelZeroSimpleTypes.{uK, uT} (k + 1) K.Carrier,
      SupercuspidalClassContainsType K π x.2 →
        Henniart.Numerical.supercuspidalTorsionNumber K π = k + 1 ∧
          Henniart.Numerical.HasSupercuspidalSwan K π 0

end Instances

end Langlands.BushnellKutzko
