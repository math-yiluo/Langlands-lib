import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.CorepresentedClosedSubgroup
import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Absolute.OppositeCellStatement

/-! # Borel subgroups, maximal tori and parabolic subgroups over a field: statements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Conjugacy of Borel subgroups** (Milne, Theorem 17.9(b)). Let `G` be a smooth affine group
scheme with connected underlying space over an algebraically closed field `k`. Then `G` has a
Borel subgroup, and for any two Borel subgroups `i : B ⟶ G` and `i' : B' ⟶ G` there are a point
`g ∈ G(k)` and an isomorphism `φ : B ≅ B'` with `i ≫ int(g) = φ ≫ i'`. -/
def BorelConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    (∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsBorelSubgroup i) ∧
      ∀ (B B' : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G) (i' : B' ⟶ G),
        IsBorelSubgroup i → IsBorelSubgroup i' →
          ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (φ : B ≅ B'),
            i ≫ (G.innerIso g).hom = φ.hom ≫ i'

/-- **Conjugacy of maximal tori** (Milne, Theorem 17.10). Let `G` be a smooth affine group
scheme with connected underlying space over an algebraically closed field `k`. For any two
maximal tori `j : T ⟶ G` and `j' : T' ⟶ G` there are a point `g ∈ G(k)` and an isomorphism
`φ : T ≅ T'` of commutative group schemes with `j ≫ int(g) = φ ≫ j'`. -/
def MaximalTorusConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T T' : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G) (j' : T'.toGrp ⟶ G),
    IsMaximalTorus j → IsMaximalTorus j' →
      ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (φ : T ≅ T'),
        j ≫ (G.innerIso g).hom = CommGroupScheme.groupHom φ.hom ≫ j'

/-- **The normalizer theorem** on `k`-points (Milne, Theorem 17.48). Let `G` be a smooth affine
group scheme with connected underlying space over an algebraically closed field `k`, and let
`i : B ⟶ G` be a Borel subgroup. The normalizer in `G(k)` of the image of `B(k)` is that
image. -/
def BorelNormalizerStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsBorelSubgroup i →
      Subgroup.normalizer
          ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
            Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) =
        (SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))

/-- **Parabolic subgroups are the dynamic `P(χ)`** (Milne, Theorem 25.1). For a connected
reductive group `G` over a field `k`, a closed subgroup `i : P ⟶ G` is parabolic if and only if
its range is the dynamic parabolic subgroup functor `P(χ)` of some cocharacter `χ : 𝔾_m ⟶ G`
defined over `k`. -/
def ParabolicDynamicStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))), IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G), IsClosedSubgroup i →
      (IsParabolicSubgroup i ↔
        ∃ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
          SubgroupFunctor.range i = Dynamic.parabolic χ)

/-- **Borel subgroups from regular cocharacters** (Milne, Proposition 21.29, Proposition 21.31
and Theorem 21.32). Let `G` be a connected reductive group over a field and `j : T ⟶ G` a maximal
torus with `T` split. Then:
* for every regular cocharacter `ν` of `j`, every closed subgroup representing `P(ν ≫ j)` is a
  Borel subgroup;
* for regular `ν` and `ν'`, `P(ν ≫ j) = P(ν' ≫ j)` if and only if `⟨α, ν⟩` and `⟨α, ν'⟩` have
  the same sign for every root `α`;
* every Borel subgroup through which `j` factors represents `P(ν ≫ j)` for some regular `ν`. -/
def RegularCocharacterBorelStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (j : T.toGrp ⟶ G), IsSplitTorus T.toGrp → IsMaximalTorus j →
      haveI := hG.isAffineHom
      (∀ ν : cocharacterLattice T, IsRegularCocharacter j ν →
        ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsClosedSubgroup i →
          (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy i →
            IsBorelSubgroup i) ∧
      (∀ ν ν' : cocharacterLattice T, IsRegularCocharacter j ν → IsRegularCocharacter j ν' →
        (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j) =
            Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ j) ↔
          ∀ α ∈ roots j, (0 < latticePairing T α ν ↔ 0 < latticePairing T α ν'))) ∧
      (∀ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G) (f : T.toGrp ⟶ B),
        IsBorelSubgroup i → f ≫ i = j →
          ∃ ν : cocharacterLattice T, IsRegularCocharacter j ν ∧
            (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy i)

/-- **The Borel subgroup of `GL_N`** (Milne, Example 17.7 and Proposition 21.29). Over every
field `k`, for every `N` and every strictly decreasing weight vector `e : Fin N → ℤ`:
* the block parabolic subgroup scheme of `e`, the upper triangular matrices, is a Borel subgroup
  of `GL_N`;
* with the diagonal torus it forms a Borel pair;
* it represents the dynamic parabolic subgroup functor of the diagonal cocharacter of `e`;
* the cocharacter of the diagonal torus with coordinates `e` is regular. -/
def GeneralLinearBorelStatement : Prop :=
  ∀ (k : Type u) [Field k] (N : ℕ) (e : Fin N → ℤ), StrictAnti e →
    IsBorelSubgroup (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) e) ∧
    IsBorelPair (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) e)
      (GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of k)) ∧
    (Dynamic.parabolic (GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of k) e)).IsRepresentedBy
      (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) e) ∧
    IsRegularCocharacter (GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of k))
      ((splitTorus.cocharacterLatticeEquiv k (ULift.{u} (Fin N))).symm fun i => e i.down)

end Langlands.GroupScheme
