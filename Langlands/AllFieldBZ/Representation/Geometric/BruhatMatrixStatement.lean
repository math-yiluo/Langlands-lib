import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.Representation.Geometric.BruhatMatrixStatement

/-!
# All-field port of `Langlands.Representation.Geometric.BruhatMatrixStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.BruhatMatrixStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding PadicBruhatMatrixExistenceTheorem PadicBruhatWeylReflectionTheorem
open Langlands.GeneralLinear
universe uF

/-- Every parabolic double coset contains the inverse matrix of an actual
permutation, without requiring that permutation to be minimal. -/
def PadicBruhatMatrixExistenceTheorem : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (n : ℕ), 0 < n → ∀ (B C : BlockShape n) (g : GeneralLinear n F.Carrier),
      ∃ w : Equiv.Perm (Fin n),
        DoubleCoset.mk (B.parabolic F.Carrier) (C.parabolic F.Carrier)
            (permutation n F.Carrier w)⁻¹ =
          DoubleCoset.mk (B.parabolic F.Carrier) (C.parabolic F.Carrier) g

/-- Equality of inverse permutation-matrix classes reflects equality of the
corresponding Weyl double cosets, with the block subgroups in reversed order. -/
def PadicBruhatWeylReflectionTheorem : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (n : ℕ), 0 < n → ∀ (B C : BlockShape n) (v w : Equiv.Perm (Fin n)),
      DoubleCoset.mk (B.parabolic F.Carrier) (C.parabolic F.Carrier)
          (permutation n F.Carrier v)⁻¹ =
        DoubleCoset.mk (B.parabolic F.Carrier) (C.parabolic F.Carrier)
          (permutation n F.Carrier w)⁻¹ →
      DoubleCoset.mk (blockWeyl C) (blockWeyl B) v =
        DoubleCoset.mk (blockWeyl C) (blockWeyl B) w

end Langlands.AllFieldBZ.Geometric
