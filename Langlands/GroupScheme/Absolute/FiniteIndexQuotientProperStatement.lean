import Langlands.GroupScheme.HomogeneousQuotientStatement
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Properness transfer from a quotient by a subgroup to a quotient by an open subgroup -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over an algebraically closed field `k`, let `G` be a smooth affine group scheme, `iS : S ⟶ G`
a closed subgroup (possibly nonreduced or disconnected), and `iH : H ⟶ G` a closed subgroup
factoring as `f ≫ iS` where the image of `f` is open in `S`. Suppose a proper scheme `O` over `k`
receives a flat, surjective, quasi-compact morphism `π : G ⟶ O` whose fibers on every test scheme
are exactly the cosets `gS`. Then every separated finite-type scheme `Q` over `k` with a smooth,
surjective, quasi-compact morphism `q : G ⟶ Q` whose fibers on every test scheme are exactly the
cosets `gH` is proper over `k`. -/
def FiniteIndexQuotientProperTransferStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (S : GroupScheme (Spec (CommRingCat.of k))) (iS : S ⟶ G),
    IsClosedSubgroup iS →
    ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (iH : H ⟶ G) (f : H ⟶ S),
      IsClosedSubgroup iH → f ≫ iS = iH → IsOpen (Set.range f.hom.hom.left) →
    ∀ (O : Over (Spec (CommRingCat.of k))) (π : G.X ⟶ O),
      IsProper O.hom → Flat π.left → Surjective π.left → QuasiCompact π.left →
      (∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
        g ≫ π = h ≫ π ↔ g⁻¹ * h ∈ (SubgroupFunctor.range iS).carrier T) →
    ∀ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q),
      IsSeparated Q.hom → LocallyOfFiniteType Q.hom → QuasiCompact Q.hom →
      Smooth q.left → Surjective q.left → QuasiCompact q.left →
      (∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
        g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range iH).carrier T) →
      IsProper Q.hom

end Langlands.GroupScheme
