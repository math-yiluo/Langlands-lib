import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.InnerAutomorphism
import Langlands.GroupScheme.Torus.Lattice

/-! # Cocharacters lie in maximal split tori; conjugacy of maximal split tori of smooth groups -/

universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over every field `k`, every cocharacter `χ : 𝔾ₘ ⟶ G` of an affine group scheme `G` locally
of finite type over `k` factors as `groupHom ν ≫ i` through a maximal split torus
`i : T ⟶ G`, for a cocharacter `ν` of `T`. -/
def CocharacterMaximalSplitTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G),
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      (ν : cocharacterLattice T),
      IsMaximalSplitTorus i ∧ CommGroupScheme.groupHom ν ≫ i = χ

/-- Over every field `k`, any two maximal split tori `i : T ⟶ G` and `i' : T' ⟶ G` of a smooth
affine group scheme `G` with connected underlying space are conjugate by a rational point:
there are `g ∈ G(k)` and an isomorphism `e : T ≅ T'` with `i ≫ int(g) = e ≫ i'`. -/
def SmoothMaximalSplitTorusConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T T' : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (i' : T'.toGrp ⟶ G), IsMaximalSplitTorus i → IsMaximalSplitTorus i' →
      ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (e : T.toGrp ≅ T'.toGrp),
        i ≫ (G.innerIso g).hom = e.hom ≫ i'

end Langlands.GroupScheme
