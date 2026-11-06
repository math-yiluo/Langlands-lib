import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Absolute.Borel
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Statement: proper quotients of reductive group schemes by parabolic subgroups -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeParabolicQuotient

/-- Over every commutative ring `R`, a reductive group scheme `G` and a smooth closed subgroup
`i : P ⟶ G` whose base change to every field is parabolic have an actual quotient `q : G → Q`:
`Q` is proper over `Spec R`, `q` is flat, surjective and quasi-compact, and on every test scheme
two points have the same image exactly when they differ on the right by a point of `P`.
This is a derived form of Conrad, *Reductive group schemes*, Corollary 5.2.8 with
Theorem 2.3.6. -/
def ExistenceStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (G P : GroupScheme (Spec (CommRingCat.of R))) (i : P ⟶ G),
    IsReductive G → Smooth P.X.hom → IsClosedImmersion i.hom.hom.left →
    (∀ (k : Type u) [Field k] [Algebra R k],
      IsParabolicSubgroup ((GroupScheme.baseChange (Spec.algebraMap R k)).map i)) →
    ∃ (Q : Over (Spec (CommRingCat.of R))) (q : G.X ⟶ Q),
      IsProper Q.hom ∧ Flat q.left ∧ Surjective q.left ∧ QuasiCompact q.left ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (g h : T ⟶ G.X),
        g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T

end Langlands.GroupScheme.RelativeParabolicQuotient
