import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.MatrixRepresentation
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Statement: smooth commutative groups with semisimple geometric points (Milne 12.21) -/

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Multiplicative type via semisimple geometric points** (Milne, *Algebraic Groups*,
Corollary 12.21). A smooth commutative affine group scheme `G` over a field `k` is of
multiplicative type if and only if `G(kᵃ)` consists of semisimple elements, where `kᵃ` is the
algebraic closure of `k`: for every representation `ρ` of `G` on `kⁿ` and every point `x` of
`G` with values in `kᵃ`, the matrix `ρ(x)` is a semisimple endomorphism of `(kᵃ)ⁿ`.

This is a statement only; nothing is proved here. -/
def MultiplicativeTypeSemisimplePointsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom],
    IsCommMonObj G.X →
      (IsMultiplicativeType G ↔
        ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n))
          (x : (algSpec (CommRingCat.of k)).obj
              (op (CommAlgCat.of (CommRingCat.of k) (AlgebraicClosure k))) ⟶ G.X),
          Module.End.IsSemisimple (Matrix.toLin'
            (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) (AlgebraicClosure k)) x :
              Matrix (Fin n) (Fin n) (AlgebraicClosure k))))

end Langlands.GroupScheme
