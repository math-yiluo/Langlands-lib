import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Statement: supplied dynamic parabolic quotients are proper over algebraically closed fields -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, every supplied separated finite-type quotient `q : G → Q`
of a connected reductive group by the dynamic parabolic `P(χ)`, with a smooth surjective
quasi-compact projection and exact right-coset fibers `gP(χ)` on every test scheme, is proper.
This is a derived form of Milne 2017, Theorem 25.1 with Definition 17.15 and A.76(b). -/
def DynamicQuotientProperStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q),
      IsSeparated Q.hom → LocallyOfFiniteType Q.hom → QuasiCompact Q.hom →
      Smooth q.left → Surjective q.left → QuasiCompact q.left →
      (∀ (Y : Over (Spec (CommRingCat.of k))) (g h : Y ⟶ G.X),
        g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (Dynamic.parabolic χ).carrier Y) →
      IsProper Q.hom

end Langlands.GroupScheme
