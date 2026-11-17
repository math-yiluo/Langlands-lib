import Langlands.AbelianScheme.IsogenySpecialization
import Langlands.AbelianScheme.AlgClosedIsogenyPoints
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # The degree of an isogeny in characteristic zero counts its kernel points -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

/-- Let `α : A ⟶ B` be an isogeny of abelian schemes over an algebraically closed field `k`
of characteristic zero. At every point `y` of `B`, the rank of the finite flat underlying
morphism of `α` equals the number of `k`-points of the kernel of `α`, that is, of the
kernel of the induced homomorphism on `k`-points. This proposition is a statement target,
not a proof. -/
def IsogenyFinrankKernelCardStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A B : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (α : A ⟶ B), IsIsogeny α → ∀ y : B.X.left,
      (hom α).finrank y =
        Nat.card (GroupScheme.pointsHom (groupHom α) (Over.mk (𝟙 _))).ker

end Langlands.AbelianScheme
