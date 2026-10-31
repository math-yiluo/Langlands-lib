import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.FieldTheory.IsAlgClosed.Basic

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- An open subset of a locally finite type group scheme over a field is closed
if its geometric points are closed under division. -/
def FieldGroupOpenSubgroupClosedStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] (U : Set G.left), IsOpen U →
    (∀ (K : Type u) [Field K] [IsAlgClosed K]
      (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) (p q : Over.mk b ⟶ G),
      Set.range p.left ⊆ U → Set.range q.left ⊆ U → Set.range (p * q⁻¹).left ⊆ U) →
    IsClosed U

end Langlands.GroupScheme
