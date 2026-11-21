import Langlands.Correspondence.HenniartTwistSwanReductionProof
import Langlands.BushnellKutzko.NormalizedLevelExistenceProof
import Langlands.BushnellKutzko.NormalizedLevelTwistProof
import Langlands.BushnellKutzko.SupercuspidalSwanLevelProof

/-! # Proof of the supercuspidal twist Swan bound

The published reduction `supercuspidalTwistSwanBoundReduction` (L0 → L2 → T2 → bound),
applied to the published proofs of L0 (`normalizedLevelExistence`), L2
(`normalizedLevelTwist`) and T2 (`supercuspidalSwanLevel`).
-/

namespace Langlands.Henniart

universe uK uV

/-- **Lemma `lem:level`(ii), supercuspidal form.** The Swan exponent `s'` of the twist of a
supercuspidal class of rank `n = k + 1` and Swan exponent `s` by `χ ∘ det` satisfies
`s' ≤ max s (n · sw(χ))`, with equality when `s ≠ n · sw(χ)`. -/
theorem supercuspidalTwistSwanBound : SupercuspidalTwistSwanBoundStatement.{uK, uV} :=
  supercuspidalTwistSwanBoundReduction BushnellKutzko.normalizedLevelExistence
    BushnellKutzko.normalizedLevelTwist BushnellKutzko.supercuspidalSwanLevel

end Langlands.Henniart
