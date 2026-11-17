import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Unipotence of smooth groups through geometric points (Milne 14.12) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 14.12: a smooth affine algebraic group `G` over a field `k` is
unipotent if and only if every element of `G(kᵃ)` is unipotent, that is, acts by a unipotent
matrix in every finite-dimensional representation of the base change `G_{kᵃ}` (Milne 14.27). -/
def SmoothUnipotentGeometricPointsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom],
    IsUnipotent G ↔
      ∀ (n : Type) [Fintype n] [DecidableEq n]
        (ρ : MatrixRepresentation ((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))).obj G) n)
        (g : Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶
          ((GroupScheme.baseChange
            (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))).obj G).X),
        IsNilpotent ((ρ.rationalMatrix g : Matrix n n (AlgebraicClosure k)) - 1)

end Langlands.GroupScheme
