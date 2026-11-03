import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Vector classification targets for smooth commutative groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- The characteristic-zero commutative-unipotent vector classification used in
CGP 3.3.11, stated over algebraically closed fields for its current consumer. -/
def CommutativeUnipotentVectorCharZeroStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (G : CommGroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
    IsUnipotent G.toGrp → IsVectorGroup G.toGrp

/-- The connected algebraically closed case of CGP B.1.10. The exponent law
is imposed on actual points of every scheme test. -/
def SmoothCommutativePTorsionVectorStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : CommGroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
    (∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X), x ^ p = 1) →
    IsVectorGroup G.toGrp

/-- The two classification inputs, without any assertion of their proofs. -/
def CommutativeVectorClassificationStatement : Prop :=
  CommutativeUnipotentVectorCharZeroStatement.{u} ∧
    SmoothCommutativePTorsionVectorStatement.{u}

end Langlands.GroupScheme.RelativeRoot
