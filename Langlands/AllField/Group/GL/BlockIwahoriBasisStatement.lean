import Langlands.Group.GL.BlockIwahoriBasisStatement
import Langlands.AllField.Group.GL.BlockIwahoriDefinitions
import Langlands.AllField.Group.GL.CompactOpen
open Filter Topology

namespace Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape hiding BlockIwahoriBasisStatement HasBlockIwahoriFactorization IsDeeplyContracting IsStrictlyContracting IsWeaklyContracting blockScalarRatio blockScalarRatio_apply isWeaklyContracting_one
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF

/-- Every identity neighborhood in the actual local-field GL contains a compact open
subgroup with the published weak-chamber block Iwahori factorization. -/
def BlockIwahoriBasisStatement {F : Type uF} [Field F]
    {n : ℕ} (B : GeneralLinear.BlockShape n) (T : LocalFieldData F) : Prop :=
  letI := T.topology
  ∀ U : Set (GeneralLinear n F), U ∈ 𝓝 (1 : GeneralLinear n F) →
    ∃ K : OpenSubgroup (GeneralLinear n F),
      IsCompact (K : Set (GeneralLinear n F)) ∧
      (K : Set (GeneralLinear n F)) ⊆ U ∧
      (Langlands.AllField.GeneralLinear.BlockShape.HasBlockIwahoriFactorization B) T K

end Langlands.AllField.GeneralLinear.BlockShape
