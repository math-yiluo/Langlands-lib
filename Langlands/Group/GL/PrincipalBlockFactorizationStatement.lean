import Langlands.Group.GL.BlockIwahoriDefinitions
import Langlands.Representation.Conductor.PrincipalCongruence

namespace Langlands.GeneralLinear.BlockShape

universe u

/-- Every positive principal congruence subgroup has unique ordered
opposite-radical, common-Levi and upper-radical factors in that subgroup. -/
def PrincipalBlockFactorizationStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (B : GeneralLinear.BlockShape (n + 1))
    (a : ℕ), 0 < a →
      Function.Bijective
        (B.iwahoriProduct k (Langlands.Conductor.principalLevelSubgroup k n a))

end Langlands.GeneralLinear.BlockShape
