import Langlands.Group.GL.UpperUnipotentCompactContainmentStatement
import Langlands.AllField.Group.GL.Padic
namespace Langlands.AllField.GeneralLinear
open Langlands.GeneralLinear hiding UpperUnipotentCompactContainmentStatement
open Langlands.AllField.GeneralLinear

universe uF

/-- Every compact subset of the actual upper-unipotent group lies in a compact
open subgroup, for each compatible local-field topology and every rank. -/
def UpperUnipotentCompactContainmentStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ),
    letI := T.topology
    ∀ C : Set (upperUnipotent n F), IsCompact C →
      ∃ K : OpenSubgroup (upperUnipotent n F),
        IsCompact (K : Set (upperUnipotent n F)) ∧
        C ⊆ (K : Set (upperUnipotent n F))

end Langlands.AllField.GeneralLinear
