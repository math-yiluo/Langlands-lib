import Langlands.AllFieldBZ.Representation.Induction.BinaryProduct
import Langlands.Representation.Smooth.FiniteLengthGrothendieckBilinear

/-! # Descent of the local-field GL induction product to exact K0 -/

namespace Langlands.Aubert

open Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.SmoothRep

universe uF uV

/-- Binary normalized induction preserves finite length and actual short exact
sequences in each variable, for all natural ranks over a local field. -/
def LocalFieldBinaryProductExactLengthStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F),
    let K := AllFieldBZ.LocalFieldPackage.ofField F
    letI : TopologicalSpace K.Carrier := T.topology
    ∀ a b : ℕ,
      let Φ := binaryNormalizedProductFunctor.{uF, max uF uV} (F := K) T a b
      PreservesFiniteLength₂ Φ ∧
        PreservesFiniteLengthShortExactLeft Φ ∧ PreservesFiniteLengthShortExactRight Φ

end Langlands.Aubert
