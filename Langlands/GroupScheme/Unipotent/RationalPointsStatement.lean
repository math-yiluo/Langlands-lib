import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.FieldTheory.Perfect

/-! # Unipotence and rational points over perfect fields (Milne 14.10) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 14.10: let `G` be an affine algebraic group over a perfect field `k`.
If `G` is unipotent, then every element of `G(k)` is unipotent (acts by a unipotent matrix in
every finite-dimensional representation); conversely, if `G(k)` is schematically dense in `G`
(no proper closed subscheme of `G` contains all `k`-points) and every element of `G(k)` is
unipotent, then `G` is unipotent. -/
def PerfectFieldUnipotentRationalPointsStatement : Prop :=
  ∀ (k : Type u) [Field k] [PerfectField k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
    let UnipotentPoints : Prop :=
      ∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)
        (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X),
        IsNilpotent ((ρ.rationalMatrix g : Matrix n n k) - 1)
    (IsUnipotent G → UnipotentPoints) ∧
      ((∀ (Z : Scheme.{u}) (z : Z ⟶ G.X.left), IsClosedImmersion z →
          (∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
            ∃ s : Spec (CommRingCat.of k) ⟶ Z, s ≫ z = g.left) → IsIso z) →
        UnipotentPoints → IsUnipotent G)

end Langlands.GroupScheme
