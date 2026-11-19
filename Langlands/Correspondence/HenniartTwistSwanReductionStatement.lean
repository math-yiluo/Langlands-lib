import Langlands.BushnellKutzko.NormalizedLevelExistenceStatement
import Langlands.BushnellKutzko.NormalizedLevelTwistStatement
import Langlands.BushnellKutzko.SupercuspidalSwanLevelStatement
import Langlands.Correspondence.HenniartTwistSwanStatement

/-!
# Reduction of the supercuspidal twist Swan bound to the level statements

The last step of the operator route note's proof of Lemma `lem:level`(ii): the bound on
Swan exponents of twists follows from the existence of normalized levels (L0), their
behaviour under twisting (L2) and the identity `sw(π) = n · ℓ(π)` for supercuspidals (T2).
-/

namespace Langlands.Henniart

/-- **Reduction.** The level statements L0 (existence of normalized levels), L2 (normalized
level of a twist by `χ ∘ det`) and T2 (Swan exponent of a supercuspidal class equals rank
times normalized level), all at the field universe `uK` and carrier universe `uV`, imply the
supercuspidal twist Swan bound at the same universes. -/
def SupercuspidalTwistSwanBoundReductionStatement.{uK, uV} : Prop :=
  BushnellKutzko.NormalizedLevelExistenceStatement.{uK, uV} →
    BushnellKutzko.NormalizedLevelTwistStatement.{uK, uV} →
      BushnellKutzko.SupercuspidalSwanLevelStatement.{uK, uV} →
        SupercuspidalTwistSwanBoundStatement.{uK, uV}

end Langlands.Henniart
