import Langlands.Representation.Geometric.WeylDefinitions

/-! Matrix existence and Weyl-class reflection prerequisites for p-adic Bruhat. -/

namespace Langlands.Geometric

open GeneralLinear

universe uF

/-- Every parabolic double coset contains the inverse matrix of an actual
permutation, without requiring that permutation to be minimal. -/
def PadicBruhatMatrixExistenceTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (n : ℕ), 0 < n → ∀ (B C : BlockShape n) (g : GeneralLinear n F.Carrier),
      ∃ w : Equiv.Perm (Fin n),
        DoubleCoset.mk (B.parabolic F.Carrier) (C.parabolic F.Carrier)
            (permutation n F.Carrier w)⁻¹ =
          DoubleCoset.mk (B.parabolic F.Carrier) (C.parabolic F.Carrier) g

/-- Equality of inverse permutation-matrix classes reflects equality of the
corresponding Weyl double cosets, with the block subgroups in reversed order. -/
def PadicBruhatWeylReflectionTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (n : ℕ), 0 < n → ∀ (B C : BlockShape n) (v w : Equiv.Perm (Fin n)),
      DoubleCoset.mk (B.parabolic F.Carrier) (C.parabolic F.Carrier)
          (permutation n F.Carrier v)⁻¹ =
        DoubleCoset.mk (B.parabolic F.Carrier) (C.parabolic F.Carrier)
          (permutation n F.Carrier w)⁻¹ →
      DoubleCoset.mk (blockWeyl C) (blockWeyl B) v =
        DoubleCoset.mk (blockWeyl C) (blockWeyl B) w

end Langlands.Geometric
