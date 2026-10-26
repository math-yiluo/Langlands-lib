import Langlands.Representation.Geometric.GeneralIntersections
import Mathlib.Basic.Complex.Basic

/-! Character determination by actual diagonal matrices on the intersection Levi. -/

namespace Langlands.Geometric

universe uF

/-- Internal algebraic statement: a complex-valued character of the actual
intersection Levi that is trivial on every actual diagonal matrix is trivial.
This proposition is stated here; its proof is a separate obligation. -/
def IntersectionLeviDiagonalCharacterStatement : Prop :=
  ∀ (F : Type uF) [Field F] [CharZero F] (n : ℕ)
    (B C : GeneralLinear.BlockShape n) (w : MinimalRepresentatives B C),
    let I := General.intersectionIn (B.leviSubgroup F) (C.leviSubgroup F)
      (GeneralLinear.permutation n F w.val)
    ∀ χ : I →* ℂˣ,
      (∀ (t : Fin n → Fˣ) (m : I),
        (m.val.val : Matrix (Fin n) (Fin n) F) =
          Matrix.diagonal (fun i => (t i : F)) → χ m = 1) →
      ∀ m : I, χ m = 1

end Langlands.Geometric
