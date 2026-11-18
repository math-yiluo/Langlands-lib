import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Algebra.CharZero.Defs

/-! # Commutative unipotent groups in characteristic zero are vector groups (Milne 16.15) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 16.15 (second sentence; see also the remark after Corollary 14.33):
over a field of characteristic zero, every commutative unipotent affine algebraic group is a
vector group, i.e. isomorphic to `G_a^n` for some `n`. -/
def CharZeroCommutativeUnipotentVectorGroupStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] [IsCommMonObj G.X],
    IsUnipotent G → RelativeRoot.IsVectorGroup G

end Langlands.GroupScheme
