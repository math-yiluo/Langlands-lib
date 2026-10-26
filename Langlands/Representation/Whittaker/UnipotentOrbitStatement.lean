import Langlands.Representation.Geometric.WeylDefinitions
import Langlands.Group.GL.SingletonBlocks
import Langlands.Group.GL.UpperUnipotent
import Langlands.Group.GL.Padic
import Langlands.Representation.Geometric.ClosedSubgroupDefinitions

/-! Concrete full-upper-unipotent orbits for an upper block parabolic. -/

namespace Langlands.Whittaker

open GeneralLinear

universe uF

/-- Inverse minimal permutation matrices parametrize the full-unipotent double
cosets and admit an ordering with open initial unions and exact representatives. -/
def UnipotentOrbitStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    ∀ (n : ℕ) (B : BlockShape (n + 1)),
      letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (n + 1)
      let P := B.parabolic F.Carrier
      let U := upperUnipotent (n + 1) F.Carrier
      Function.Bijective
        (fun w : Geometric.MinimalRepresentatives B (BlockShape.singletons (n + 1)) =>
          (DoubleCoset.mk P U (permutation (n + 1) F.Carrier w.val)⁻¹ :
            DoubleCoset.Quotient (P : Set (GeneralLinear (n + 1) F.Carrier))
              (U : Set (GeneralLinear (n + 1) F.Carrier)))) ∧
      ∃ (m : ℕ) (s : Geometric.OrderedDoubleCosets P U m)
        (e : Fin m ≃ Geometric.MinimalRepresentatives B (BlockShape.singletons (n + 1))),
        ∀ i, s.representative i = permutation (n + 1) F.Carrier (e i).val

end Langlands.Whittaker
