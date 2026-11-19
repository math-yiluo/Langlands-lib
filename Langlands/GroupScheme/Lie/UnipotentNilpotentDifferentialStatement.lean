import Langlands.GroupScheme.Lie.RepresentationDifferential
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Unipotence via nilpotent differentials of representations (Milne 16.61) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 16.61, conditions (a), (c) and (d): for a smooth connected affine group
`G` over a field `k`, the following are equivalent: (a) `G` is unipotent; (c) for every
representation `ρ` of `G`, the differential sends every element of the Lie algebra to a nilpotent
matrix; (d) the condition in (c) holds for one faithful (closed-immersion) representation.
Condition (b) of the source is not part of this statement. -/
def UnipotentNilpotentDifferentialStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    (IsUnipotent G ↔
      ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)) (X : lieKernel G k),
        IsNilpotent (ρ.tangentMatrix k X)) ∧
    (IsUnipotent G ↔
      ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), IsClosedSubgroup ρ ∧
        ∀ X : lieKernel G k, IsNilpotent (ρ.tangentMatrix k X))

end Langlands.GroupScheme
