import Langlands.Representation.Geometric.WeylDefinitions
import Langlands.Representation.CuspidalSupport.FiniteBlockShapes

/-! The signed type-A Solomon coefficient identity for actual block Weyl intersections. -/

namespace Langlands.Geometric

/-- For a standard shape `K` whose Young subgroup lies in that of `B`, the signed count,
over every ordered positive shape `C`, of the minimal representatives `w` of `(B, C)`
with `W_B ∩ w⁻¹ W_C w = W_K` is `(-1) ^ (n - K.length)`. -/
def TypeASolomonCoefficientStatement : Prop :=
  ∀ (n : ℕ) (B K : GeneralLinear.BlockShape n),
    letI : Fintype (GeneralLinear.BlockShape n) :=
      Fintype.ofFinite (GeneralLinear.BlockShape n)
    Geometric.blockWeyl K ≤ Geometric.blockWeyl B →
      (∑ C : GeneralLinear.BlockShape n,
        ((-1 : ℤ) ^ (n - C.length)) *
          (Nat.card {w : Geometric.MinimalRepresentatives B C //
            Geometric.blockWeyl B ⊓
              (Geometric.blockWeyl C).comap
                (MulAut.conj w.val).toMonoidHom =
                  Geometric.blockWeyl K} : ℤ)) =
        (-1 : ℤ) ^ (n - K.length)

end Langlands.Geometric
