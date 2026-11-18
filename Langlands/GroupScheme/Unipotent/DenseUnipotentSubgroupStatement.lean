import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Algebraic subgroups of `GL_V` with a dense unipotent subgroup (Milne 14.11) -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 14.11: let `G` be an algebraic subgroup of `GL_n` over a field `k`
(the homomorphism `ρ : G ⟶ GL_n` is a closed immersion). If some subgroup `S` of `G(k)` is
schematically dense in `G` (every closed subscheme of `G` through which all points of `S`
factor is all of `G`) and consists of unipotent matrices, then `G` is unipotent. -/
def GeneralLinearDenseUnipotentSubgroupStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (n : Type) [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n),
    IsClosedSubgroup ρ →
    ∀ S : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X),
      (∀ (Z : Scheme.{u}) (z : Z ⟶ G.X.left), IsClosedImmersion z →
          (∀ g ∈ S, ∃ s : Spec (CommRingCat.of k) ⟶ Z, s ≫ z = g.left) → IsIso z) →
      (∀ g ∈ S, IsNilpotent ((ρ.rationalMatrix g : Matrix n n k) - 1)) →
      IsUnipotent G

end Langlands.GroupScheme
