import Langlands.Representation.Whittaker.UnipotentOrbitStatement
import Langlands.AllField.Group.GL.SingletonBlocks
/-! Concrete full-upper-unipotent orbits for an upper block parabolic. -/

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding UnipotentOrbitStatement
open Langlands.AllField.Whittaker

open Langlands.GeneralLinear

universe uF

/-- Inverse minimal permutation matrices parametrize the full-unipotent double
cosets and admit an ordering with open initial unions and exact representatives. -/
def UnipotentOrbitStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape (n + 1)),
      letI := T.generalLinearTopologicalGroup (n + 1)
      let P := B.parabolic F
      let U := upperUnipotent (n + 1) F
      Function.Bijective
        (fun w : Geometric.MinimalRepresentatives B (BlockShape.singletons (n + 1)) =>
          (DoubleCoset.mk P U (permutation (n + 1) F w.val)⁻¹ :
            DoubleCoset.Quotient (P : Set (GeneralLinear (n + 1) F))
              (U : Set (GeneralLinear (n + 1) F)))) ∧
      ∃ (m : ℕ) (s : Geometric.OrderedDoubleCosets P U m)
        (e : Fin m ≃ Geometric.MinimalRepresentatives B (BlockShape.singletons (n + 1))),
        ∀ i, s.representative i = permutation (n + 1) F (e i).val

end Langlands.AllField.Whittaker
