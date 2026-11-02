import Langlands.GroupScheme.Torus.Maximal

/-! # Solvable, Borel and parabolic subgroups of group schemes over a field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-! ### Solvable group schemes -/

/-- A group scheme `G` over a field `k` is solvable when the abstract group `G_{k̄}(k̄)` of points
of the base change `G_{k̄}` over `Spec k̄`, for `k̄` the algebraic closure of `k`, is solvable.
This notion is only used for smooth group schemes. -/
def IsSolvableGroupScheme (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶
    ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X)

/-! ### Borel subgroups -/

/-- A closed subgroup `i : B ⟶ G` over a field is a Borel subgroup when `B` is smooth, connected
and solvable, and `i` does not factor through a strictly larger smooth connected solvable closed
subgroup: whenever `i = f ≫ i'` with `i' : B' ⟶ G` such a closed subgroup, `f` is an
isomorphism. -/
structure IsBorelSubgroup {B G : GroupScheme (Spec (CommRingCat.of k))} (i : B ⟶ G) : Prop where
  isClosedSubgroup : IsClosedSubgroup i
  smooth : Smooth B.X.hom
  connectedSpace : ConnectedSpace B.X.left
  isSolvableGroupScheme : IsSolvableGroupScheme B
  maximal : ∀ (B' : GroupScheme (Spec (CommRingCat.of k))) (i' : B' ⟶ G) (f : B ⟶ B'),
    IsClosedSubgroup i' → Smooth B'.X.hom → ConnectedSpace B'.X.left →
      IsSolvableGroupScheme B' → f ≫ i' = i → IsIso f

/-! ### Parabolic subgroups -/

/-- A smooth closed subgroup `i : P ⟶ G` over a field `k` is parabolic when some Borel subgroup
`j : B ⟶ G_{k̄}` of the base change of `G` to the algebraic closure `k̄` factors through the base
change `i_{k̄} : P_{k̄} ⟶ G_{k̄}` of `i`. -/
structure IsParabolicSubgroup {P G : GroupScheme (Spec (CommRingCat.of k))} (i : P ⟶ G) :
    Prop where
  isClosedSubgroup : IsClosedSubgroup i
  smooth : Smooth P.X.hom
  exists_isBorelSubgroup : ∃ (B : GroupScheme (Spec (CommRingCat.of (AlgebraicClosure k))))
    (j : B ⟶ (GroupScheme.baseChange (toAlgebraicClosure k)).obj G)
    (f : B ⟶ (GroupScheme.baseChange (toAlgebraicClosure k)).obj P),
    IsBorelSubgroup j ∧ f ≫ (GroupScheme.baseChange (toAlgebraicClosure k)).map i = j

/-! ### Borel pairs -/

/-- A Borel pair `(i, j)`: `i : B ⟶ G` is a Borel subgroup, `j : T ⟶ G` is a maximal torus, and
`j` factors through `i`. -/
def IsBorelPair {B G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : B ⟶ G) (j : T.toGrp ⟶ G) : Prop :=
  IsBorelSubgroup i ∧ IsMaximalTorus j ∧ ∃ f : T.toGrp ⟶ B, f ≫ i = j

/-! ### Regular cocharacters -/

/-- A cocharacter `ν` of `T` is regular for `j : T ⟶ G` when `⟨α, ν⟩ ≠ 0` for every root `α` of
`T` in `G` through `j`. -/
def IsRegularCocharacter {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] (j : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) : Prop :=
  ∀ α ∈ roots j, latticePairing T α ν ≠ 0

end Langlands.GroupScheme
