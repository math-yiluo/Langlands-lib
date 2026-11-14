import Langlands.AllFieldBZ.Group.GL.BlockIwahoriDefinitions
import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.Group.GL.InverseTransposeIwahoriStatement

/-!
# All-field port of `Langlands.Group.GL.InverseTransposeIwahoriStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.InverseTransposeIwahoriStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
universe uF u

section Ring
variable {n : ℕ} (B : GeneralLinear.BlockShape n) (R : Type u) [CommRing R]

end Ring
section Padic
variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- The open comap of a compact open subgroup by the supplied continuous inverse
transpose is compact. -/
def _root_.Langlands.GeneralLinear.BlockShape.InverseTransposeCompactComapClause_allFieldBZ (n : ℕ) : Prop :=
  letI := T.topology
  ∀ K : OpenSubgroup (GeneralLinear n F.Carrier),
    IsCompact (K : Set (GeneralLinear n F.Carrier)) →
      IsCompact ((K.comap (T.generalLinearInverseTranspose n).toMonoidHom
          (T.generalLinearInverseTranspose n).continuous :
        OpenSubgroup (GeneralLinear n F.Carrier)) : Set (GeneralLinear n F.Carrier))

/-- The published weak-chamber block Iwahori factorization, for the same shape,
passes from an open subgroup to its comap by the supplied continuous inverse
transpose. -/
def _root_.Langlands.GeneralLinear.BlockShape.InverseTransposeIwahoriFactorizationClause_allFieldBZ {n : ℕ}
    (B : GeneralLinear.BlockShape n) : Prop :=
  letI := T.topology
  ∀ K : OpenSubgroup (GeneralLinear n F.Carrier),
    B.HasBlockIwahoriFactorization_allFieldBZ T K →
      B.HasBlockIwahoriFactorization_allFieldBZ T
        (K.comap (T.generalLinearInverseTranspose n).toMonoidHom
          (T.generalLinearInverseTranspose n).continuous)

end Padic
end Langlands.AllFieldBZ.GeneralLinear.BlockShape
