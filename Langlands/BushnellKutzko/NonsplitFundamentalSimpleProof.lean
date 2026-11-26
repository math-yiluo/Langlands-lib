import Langlands.BushnellKutzko.NonsplitFundamentalSimpleLocal
import Langlands.BushnellKutzko.NonsplitFundamentalSimpleTransport
import Langlands.BushnellKutzko.SubfieldIntegerArithmetic

/-! # Proof of the semisimplicity criterion for nonsplit fundamental strata (BK93 (2.4.13)) -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uE uV

/-- **BK93 (2.4.13)**: a nonsplit fundamental stratum `[𝔄, n, n-1, b]` with `n ≥ 1` is
equivalent to a simple stratum on the same chain and levels if and only if its residue
centralizer is semisimple, over `𝔬_F` and over the integral closure of `𝔬_F` in a finite
extension. -/
theorem nonsplitFundamentalSimple : NonsplitFundamentalSimpleStatement.{uF, uE, uV} := by
  intro F _ _ _ _
  refine ⟨fun V _ _ _ S => NonsplitSimple.nonsplitSimpleCriterion_integer S, ?_⟩
  intro E _ _ _ V _ _ _ S
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  have := LocalField.FiniteExtension.isLocalField F E
  let φ := subfieldIntegerEquiv F E
  have hφ : ∀ a, algebraMap 𝒪[E] E (φ a) = algebraMap (subfieldIntegers F E) E a := fun _ => rfl
  have hinj : Function.Injective (algebraMap 𝒪[E] E) := Subtype.val_injective
  let S' := NonsplitSimple.transportStratum φ hφ S
  have hb : S.b ∈ S.chain.endFiltration (-S.n) :=
    NonsplitRefinement.mem_of_le_valuation S'.chain (by exact_mod_cast S'.valuation_ge)
  exact NonsplitSimple.nonsplitSimpleCriterion_of_transport φ hφ S hinj hb
    (NonsplitSimple.nonsplitSimpleCriterion_integer S')

end Langlands.BushnellKutzko
