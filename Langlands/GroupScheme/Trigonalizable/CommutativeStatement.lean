import Langlands.GroupScheme.Trigonalizable
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Commutative groups over algebraically closed fields are trigonalizable (Milne 16.14) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 16.14: every commutative affine algebraic group over an algebraically
closed field is trigonalizable. -/
def AlgClosedCommutativeTrigonalizableStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] [IsCommMonObj G.X],
    IsTrigonalizable G

end Langlands.GroupScheme
