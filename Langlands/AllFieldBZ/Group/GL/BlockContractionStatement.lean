import Langlands.AllFieldBZ.Group.GL.BlockIwahoriDefinitions
import Langlands.AllFieldBZ.Group.GL.PadicBlocks
import Langlands.Group.GL.BlockContractionStatement

/-!
# All-field port of `Langlands.Group.GL.BlockContractionStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.BlockContractionStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
open scoped Topology
namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
universe uF

variable {n : ℕ} (B : GeneralLinear.BlockShape n)
  {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- Every positive depth bound admits an actual block-scalar tuple. -/
def _root_.Langlands.GeneralLinear.BlockShape.DeepChamberNonempty_allFieldBZ : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ a : Fin B.length → F.Carrierˣ, B.IsDeeplyContracting_allFieldBZ T ε a

/-- One positive depth bound contracts both compact sets for every deep tuple. -/
def _root_.Langlands.GeneralLinear.BlockShape.UniformCompactBlockContraction_allFieldBZ : Prop :=
  letI := T.topology
  ∀ Cplus Cminus : Set (GeneralLinear n F.Carrier),
    IsCompact Cplus →
    Cplus ⊆ (B.unipotentSubgroup F.Carrier : Set (GeneralLinear n F.Carrier)) →
    IsCompact Cminus →
    Cminus ⊆
      (B.oppositeUnipotentSubgroup F.Carrier : Set (GeneralLinear n F.Carrier)) →
    ∀ U : Set (GeneralLinear n F.Carrier), U ∈ 𝓝 (1 : GeneralLinear n F.Carrier) →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
        ∀ a : Fin B.length → F.Carrierˣ, B.IsDeeplyContracting_allFieldBZ T ε a →
          (∀ x ∈ Cplus,
            B.blockScalar F.Carrier a * x * (B.blockScalar F.Carrier a)⁻¹ ∈ U) ∧
          (∀ y ∈ Cminus,
            (B.blockScalar F.Carrier a)⁻¹ * y * B.blockScalar F.Carrier a ∈ U)

/-- Every sufficiently high pointwise power of a strict tuple is arbitrarily deep. -/
def _root_.Langlands.GeneralLinear.BlockShape.StrictPowersEventuallyDeep_allFieldBZ : Prop :=
  ∀ a : Fin B.length → F.Carrierˣ, B.IsStrictlyContracting_allFieldBZ T a →
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℕ, ∀ s : ℕ, r ≤ s →
        B.IsDeeplyContracting_allFieldBZ T ε (fun i => (a i) ^ s)

end Langlands.AllFieldBZ.GeneralLinear.BlockShape
