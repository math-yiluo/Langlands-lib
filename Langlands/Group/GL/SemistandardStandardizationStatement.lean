import Langlands.Representation.Exponents.ParabolicPair
import Langlands.Group.GL.SingletonBlocks
import Langlands.Group.GL.Maps

/-! Permutation standardization of a semistandard GL block pair. -/

namespace Langlands

open GeneralLinear Exponents

universe uF

/-- Inclusion of the actual conjugated block-scalar subgroup in the fixed
coordinate diagonal subgroup makes the conjugator block diagonal after an
actual row permutation, with the original ordered block shape. -/
def GLSemistandardStandardizationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (n : ℕ)
    (P : ConjugateBlockPair n F.Carrier),
    P.splitComponent ≤
      (ConjugateBlockPair.standard (R := F.Carrier)
        (BlockShape.singletons n)).splitComponent →
    ∃ (w : Equiv.Perm (Fin n)) (m : P.shape.Levi F.Carrier),
      GeneralLinear.permutation n F.Carrier w * P.conjugator =
        P.shape.leviEmbedding F.Carrier m

end Langlands
