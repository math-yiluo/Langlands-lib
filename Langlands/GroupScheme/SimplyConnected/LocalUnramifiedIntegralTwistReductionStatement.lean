import Langlands.GroupScheme.SimplyConnected.LocalUnramifiedIntegralTwistStatement
import Langlands.GroupScheme.SimplyConnected.LocalUnramifiedCocycleVanishingStatement

/-! # Integral twists give vanishing on finite unramified covers: the statement -/

universe u

namespace Langlands.GroupScheme

/-- The twisting statement `LocalSimplyConnectedUnramifiedIntegralTwistStatement` (the building
step of Kaletha–Prasad, Theorems 10.6.1 and 10.6.4) implies that every cocycle of a semisimple
simply connected group over a nonarchimedean local field, on a finite unramified cover, is
trivial. -/
def LocalSimplyConnectedUnramifiedIntegralTwistReductionStatement : Prop :=
  LocalSimplyConnectedUnramifiedIntegralTwistStatement.{u} →
    LocalSimplyConnectedUnramifiedCocycleVanishingStatement.{u}

end Langlands.GroupScheme
