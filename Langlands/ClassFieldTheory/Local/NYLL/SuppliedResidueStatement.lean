import Langlands.LocalField.Normalization.Definitions

/-! # Supplied residue equality and the discrete valuation -/

namespace Langlands.LocalClassField.NYLL

universe u

/-- Equality in the actual supplied residue field is congruence measured by
the supplied discrete valuation, for every pair of integral elements. -/
def SuppliedResidueCongruenceStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)
    (x y : T.Integers),
    T.residue x = T.residue y ↔
      T.discreteValuation ((x : F.Carrier) - (y : F.Carrier)) < 1

end Langlands.LocalClassField.NYLL
