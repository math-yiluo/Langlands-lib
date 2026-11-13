import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Langlands.AlgebraicGeometry.Picard.LineBundle
import Langlands.GroupScheme.RelativeLevi.Borel
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.InnerAutomorphism

/-! # Statement: isomorphisms of reductive groups with split maximal tori and Borel subgroups
over a connected base with trivial Picard group -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Pairs and triples with split maximal tori are isomorphic** (Conrad, *Reductive group
schemes* (2014), Proposition 6.2.11(2)). Let `S` be a connected scheme with `Pic(S) = 1`.
1. Let `G`, `G'` be reductive group schemes over `S` that are isomorphic étale-locally on `S`,
   with split maximal tori `t : 𝔾_m^I → G` and `t' : 𝔾_m^{I'} → G'`. Then some isomorphism
   `G ≅ G'` carries `T` onto `T'`, and for all Borel subgroups `B ⊇ T` of `G` and `B' ⊇ T'` of
   `G'` some isomorphism `G ≅ G'` carries `T` onto `T'` and `B` onto `B'`.
2. If moreover `S` is affine and `G' = G`, these isomorphisms can be chosen to be conjugation
   by a point `g ∈ G(S)`. -/
def ReductiveSplitTorusBorelIsomorphismStatement : Prop :=
  ∀ (S : Scheme.{u}), ConnectedSpace S →
    (∀ L : Langlands.AlgebraicGeometry.Picard.LineBundle S,
      Nonempty (L ≅ Langlands.AlgebraicGeometry.Picard.LineBundle.trivial S)) →
    (∀ (G G' : GroupScheme S), IsReductive G → IsReductive G' →
      (∃ 𝒱 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
        ∀ j : 𝒱.I₀,
          Nonempty ((GroupScheme.baseChange (𝒱.f j)).obj G ≅
            (GroupScheme.baseChange (𝒱.f j)).obj G')) →
      ∀ (I I' : Type u) [Finite I] [Finite I']
        (t : splitTorus S I ⟶ G) (t' : splitTorus S I' ⟶ G'),
        IsClosedSubgroup t → IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) t →
        IsClosedSubgroup t' →
        IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I') t' →
        (∃ Φ : G ≅ G', SubgroupFunctor.range (t ≫ Φ.hom) = SubgroupFunctor.range t') ∧
        ∀ (B B' : GroupScheme S) (i : B ⟶ G) (i' : B' ⟶ G'),
          IsRelativeBorelSubgroup i → IsRelativeBorelSubgroup i' →
          SubgroupFunctor.range t ≤ SubgroupFunctor.range i →
          SubgroupFunctor.range t' ≤ SubgroupFunctor.range i' →
          ∃ Φ : G ≅ G', SubgroupFunctor.range (t ≫ Φ.hom) = SubgroupFunctor.range t' ∧
            SubgroupFunctor.range (i ≫ Φ.hom) = SubgroupFunctor.range i') ∧
    (IsAffine S → ∀ (G : GroupScheme S), IsReductive G →
      ∀ (I I' : Type u) [Finite I] [Finite I']
        (t : splitTorus S I ⟶ G) (t' : splitTorus S I' ⟶ G),
        IsClosedSubgroup t → IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I) t →
        IsClosedSubgroup t' →
        IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme S I') t' →
        (∃ g : Over.mk (𝟙 S) ⟶ G.X,
          SubgroupFunctor.range (t ≫ (G.innerIso g).hom) = SubgroupFunctor.range t') ∧
        ∀ (B B' : GroupScheme S) (i : B ⟶ G) (i' : B' ⟶ G),
          IsRelativeBorelSubgroup i → IsRelativeBorelSubgroup i' →
          SubgroupFunctor.range t ≤ SubgroupFunctor.range i →
          SubgroupFunctor.range t' ≤ SubgroupFunctor.range i' →
          ∃ g : Over.mk (𝟙 S) ⟶ G.X,
            SubgroupFunctor.range (t ≫ (G.innerIso g).hom) = SubgroupFunctor.range t' ∧
            SubgroupFunctor.range (i ≫ (G.innerIso g).hom) = SubgroupFunctor.range i')

end Langlands.GroupScheme
