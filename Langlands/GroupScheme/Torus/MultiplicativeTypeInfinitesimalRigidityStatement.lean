import Langlands.GroupScheme.Torus.RelativeMultiplicativeType

/-! # Statement: infinitesimal rigidity of homomorphisms from groups of multiplicative type -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Infinitesimal rigidity** (Conrad, *Reductive group schemes* (2014), Corollary B.2.7;
SGA 3, IX, Corollaire 3.5). Let `S = Spec A`, let `J` be a nilpotent ideal of `A` and
`S₀ = Spec (A/J)`. A homomorphism `f : H ⟶ G` from an `S`-group `H` of multiplicative type
to an arbitrary `S`-group scheme `G` is trivial if its base change `f₀ : H_{S₀} ⟶ G_{S₀}` is
trivial. Here a homomorphism is trivial when its underlying morphism of schemes is the
identity element `1` of the group of morphisms into the group object. -/
def MultiplicativeTypeInfinitesimalRigidityStatement : Prop :=
  ∀ (A : Type u) [CommRing A] (J : Ideal A), IsNilpotent J →
    ∀ (G H : GroupScheme (Spec (CommRingCat.of A))) (f : H ⟶ G),
      RelativeMultiplicativeType.IsMultiplicativeType H →
        ((GroupScheme.baseChange (Spec.algebraMap A (A ⧸ J))).map f).hom.hom = 1 →
          f.hom.hom = 1

end Langlands.GroupScheme
