import Langlands.Representation.Classification.UnitaryGenericExhaustionReduction
import Langlands.Representation.Classification.TadicUnitaryDualExhaustionProof

/-! # Unitary generic exhaustion

Every generic irreducible unitarizable smooth representation of `GL_(n+1)` over a
p-adic field is isomorphic to the normalized twisted product of valid unitary
generic parameters (Tadic 1986, Theorem D(i)). The proof applies the published
reduction `unitaryGenericExhaustion_of_tadicUnitaryDualExhaustion` to the
published generic-free Tadic exhaustion `tadicUnitaryDualExhaustion`.
-/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- **Unitary generic exhaustion.** Every generic unitarizable smooth
representation of positive rank is isomorphic to the entire twisted normalized
product of actual valid unitary generic parameters with strict Hermitian
exponents. -/
theorem unitaryGenericExhaustion : UnitaryGenericExhaustion.{uF, uV} F T :=
  unitaryGenericExhaustion_of_tadicUnitaryDualExhaustion.{uF, uV} F T
    (tadicUnitaryDualExhaustion.{uF, uV} F T)

end Langlands.Classification
