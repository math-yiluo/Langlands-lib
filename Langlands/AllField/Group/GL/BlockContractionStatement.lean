import Langlands.Group.GL.BlockContractionStatement
import Langlands.AllField.Group.GL.BlockIwahoriDefinitions
import Langlands.AllField.Group.GL.PadicBlocks
open scoped Topology

namespace Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape hiding DeepChamberNonempty HasBlockIwahoriFactorization IsDeeplyContracting IsStrictlyContracting IsWeaklyContracting StrictPowersEventuallyDeep UniformCompactBlockContraction blockScalarRatio blockScalarRatio_apply isWeaklyContracting_one
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF

variable {n : ℕ} (B : GeneralLinear.BlockShape n)
  {F : Type uF} [Field F] (T : LocalFieldData F)

/-- Every positive depth bound admits an actual block-scalar tuple. -/
def DeepChamberNonempty : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ a : Fin B.length → Fˣ, (Langlands.AllField.GeneralLinear.BlockShape.IsDeeplyContracting B) T ε a

/-- One positive depth bound contracts both compact sets for every deep tuple. -/
def UniformCompactBlockContraction : Prop :=
  letI := T.topology
  ∀ Cplus Cminus : Set (GeneralLinear n F),
    IsCompact Cplus →
    Cplus ⊆ (B.unipotentSubgroup F : Set (GeneralLinear n F)) →
    IsCompact Cminus →
    Cminus ⊆
      (B.oppositeUnipotentSubgroup F : Set (GeneralLinear n F)) →
    ∀ U : Set (GeneralLinear n F), U ∈ 𝓝 (1 : GeneralLinear n F) →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
        ∀ a : Fin B.length → Fˣ, (Langlands.AllField.GeneralLinear.BlockShape.IsDeeplyContracting B) T ε a →
          (∀ x ∈ Cplus,
            B.blockScalar F a * x * (B.blockScalar F a)⁻¹ ∈ U) ∧
          (∀ y ∈ Cminus,
            (B.blockScalar F a)⁻¹ * y * B.blockScalar F a ∈ U)

/-- Every sufficiently high pointwise power of a strict tuple is arbitrarily deep. -/
def StrictPowersEventuallyDeep : Prop :=
  ∀ a : Fin B.length → Fˣ, (Langlands.AllField.GeneralLinear.BlockShape.IsStrictlyContracting B) T a →
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℕ, ∀ s : ℕ, r ≤ s →
        (Langlands.AllField.GeneralLinear.BlockShape.IsDeeplyContracting B) T ε (fun i => (a i) ^ s)

end Langlands.AllField.GeneralLinear.BlockShape
