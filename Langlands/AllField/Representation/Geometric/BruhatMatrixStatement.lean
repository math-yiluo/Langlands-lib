import Langlands.Representation.Geometric.BruhatMatrixStatement
import Langlands.AllField.Group.GL.Padic
/-! Matrix existence and Weyl-class reflection prerequisites for local-field Bruhat. -/

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding PadicBruhatMatrixExistenceTheorem PadicBruhatWeylReflectionTheorem
open Langlands.AllField.Geometric

open Langlands.GeneralLinear

universe uF

/-- Every parabolic double coset contains the inverse matrix of an actual
permutation, without requiring that permutation to be minimal. -/
def PadicBruhatMatrixExistenceTheorem : Prop :=
  ∀ (F : Type uF) [Field F]
    (n : ℕ), 0 < n → ∀ (B C : BlockShape n) (g : GeneralLinear n F),
      ∃ w : Equiv.Perm (Fin n),
        DoubleCoset.mk (B.parabolic F) (C.parabolic F)
            (permutation n F w)⁻¹ =
          DoubleCoset.mk (B.parabolic F) (C.parabolic F) g

/-- Equality of inverse permutation-matrix classes reflects equality of the
corresponding Weyl double cosets, with the block subgroups in reversed order. -/
def PadicBruhatWeylReflectionTheorem : Prop :=
  ∀ (F : Type uF) [Field F]
    (n : ℕ), 0 < n → ∀ (B C : BlockShape n) (v w : Equiv.Perm (Fin n)),
      DoubleCoset.mk (B.parabolic F) (C.parabolic F)
          (permutation n F v)⁻¹ =
        DoubleCoset.mk (B.parabolic F) (C.parabolic F)
          (permutation n F w)⁻¹ →
      DoubleCoset.mk (blockWeyl C) (blockWeyl B) v =
        DoubleCoset.mk (blockWeyl C) (blockWeyl B) w

end Langlands.AllField.Geometric
