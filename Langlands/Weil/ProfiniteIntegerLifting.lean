import Langlands.Weil.Pullback
import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# The universe-polymorphic lifting property of the profinite integers

This proposition states an internal universal-property interface for the actual
profinite completion used by `Langlands.Weil.Pullback`. Its proof is separate.
-/

namespace Langlands.Weil

universe u

/-- Every homomorphism from the integer group to a compact Hausdorff
nonarchimedean group extends uniquely across the canonical map into the
profinite integers. The target may lie in any universe. -/
def ProfiniteIntegerLifting : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] [CompactSpace G] [T2Space G]
    (f : Degree →* G),
    ∃! F : ProfiniteIntegers →ₜ* G,
      F.toMonoidHom.comp frobenius.toMonoidHom = f

end Langlands.Weil
