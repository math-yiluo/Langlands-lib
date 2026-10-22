import Langlands.Group.GL.BlockIwahoriDefinitions
import Langlands.Group.GL.PadicOppositeBlocks

open scoped Topology

namespace Langlands.GeneralLinear.BlockShape

universe uF

variable {n : ℕ} (B : GeneralLinear.BlockShape n)
  {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Every positive depth bound admits an actual block-scalar tuple. -/
def DeepChamberNonempty : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ a : Fin B.length → F.Carrierˣ, B.IsDeeplyContracting T ε a

/-- One positive depth bound contracts both compact sets for every deep tuple. -/
def UniformCompactBlockContraction : Prop :=
  letI := T.topology
  ∀ Cplus Cminus : Set (GeneralLinear n F.Carrier),
    IsCompact Cplus →
    Cplus ⊆ (B.unipotentSubgroup F.Carrier : Set (GeneralLinear n F.Carrier)) →
    IsCompact Cminus →
    Cminus ⊆
      (B.oppositeUnipotentSubgroup F.Carrier : Set (GeneralLinear n F.Carrier)) →
    ∀ U : Set (GeneralLinear n F.Carrier), U ∈ 𝓝 (1 : GeneralLinear n F.Carrier) →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
        ∀ a : Fin B.length → F.Carrierˣ, B.IsDeeplyContracting T ε a →
          (∀ x ∈ Cplus,
            B.blockScalar F.Carrier a * x * (B.blockScalar F.Carrier a)⁻¹ ∈ U) ∧
          (∀ y ∈ Cminus,
            (B.blockScalar F.Carrier a)⁻¹ * y * B.blockScalar F.Carrier a ∈ U)

/-- Every sufficiently high pointwise power of a strict tuple is arbitrarily deep. -/
def StrictPowersEventuallyDeep : Prop :=
  ∀ a : Fin B.length → F.Carrierˣ, B.IsStrictlyContracting T a →
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℕ, ∀ s : ℕ, r ≤ s →
        B.IsDeeplyContracting T ε (fun i => (a i) ^ s)

/-- Uniform scalar contraction for every supplied p-adic realization and block shape. -/
def BlockContractionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B : GeneralLinear.BlockShape n),
    B.DeepChamberNonempty T ∧
    B.UniformCompactBlockContraction T ∧
    B.StrictPowersEventuallyDeep T

end Langlands.GeneralLinear.BlockShape
