import Langlands.Group.GL.ReverseBlocks
import Langlands.Group.GL.SingletonBlocks
import Langlands.Representation.Geometric.WeylDefinitions
import Langlands.Representation.Geometric.ClosedSubgroupDefinitions
import Langlands.Representation.Whittaker.EntrywiseCharacter

namespace Langlands.Whittaker

open GeneralLinear

universe uK

/-- Every non-open minimal representative admits an upper-unipotent stabilizer
element detected by the generic character whose conjugate has trivial Levi image. -/
def NonOpenCharacterWitnessStatement : Prop :=
  ∀ (K : Type uK) [Field K] (n : ℕ) (B : BlockShape (n + 1))
    (ψ : AddChar K ℂ), ψ ≠ 1 →
    ∀ v : Geometric.MinimalRepresentatives B (BlockShape.singletons (n + 1)),
      v.val ≠ B.reversePermutation.symm →
      let P := B.parabolic K
      let U := upperUnipotent (n + 1) K
      let w := permutation (n + 1) K v.val
      ∃ q : Geometric.orbitStabilizer P U w,
        B.leviProjection K (Geometric.stabilizerToInducing P U w q) = 1 ∧
          entrywiseCharacter ψ (n + 1) q.val ≠ 1

end Langlands.Whittaker
