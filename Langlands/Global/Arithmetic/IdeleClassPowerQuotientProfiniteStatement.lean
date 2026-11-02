import Langlands.Global.Adelic
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Profinite quotients of actual idele classes by positive powers
-/

universe u

namespace Langlands.Global

/-- Actual idele classes modulo their positive `m`th-power subgroup, with
the quotient topology, form a Hausdorff compact totally disconnected group. -/
def IdeleClassPowerQuotientProfiniteStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (m : ℕ), 0 < m →
    T2Space (IdeleClasses K ⧸
      (powMonoidHom (α := IdeleClasses K) m).range) ∧
    CompactSpace (IdeleClasses K ⧸
      (powMonoidHom (α := IdeleClasses K) m).range) ∧
    TotallyDisconnectedSpace (IdeleClasses K ⧸
      (powMonoidHom (α := IdeleClasses K) m).range)

end Langlands.Global
