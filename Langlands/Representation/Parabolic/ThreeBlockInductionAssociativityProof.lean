import Langlands.Representation.Parabolic.ThreeBlockRegroupingAssembly
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof

/-! Proof of literal heterogeneous three-block induction associativity. -/

namespace Langlands.Parabolic

universe uF uV0 uV1 uV2

/-- The two bracketings of normalized induction of three smooth blocks are equivalent after the
entry-preserving rank transport along `Nat.add_assoc`. -/
theorem threeBlockInductionAssociativity :
    ThreeBlockInductionAssociativityStatement.{uF, uV0, uV1, uV2} :=
  threeBlockInductionAssociativity_of_common
    (commonUniverseThreeBlockAssociativity_of_regrouping.{uF, max uV0 uV1 uV2}
      (fun _ _ F => orderedProductRegrouping.{uF, max uF uV0 uV1 uV2}
        F F.canonicalTopologicalData))

end Langlands.Parabolic
