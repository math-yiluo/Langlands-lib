import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.InnerAutomorphism

/-! # Statement: lifting homomorphisms from groups of multiplicative type through nilpotent thickenings -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Infinitesimal lifting of homomorphisms** (SGA 3, IX, Théorème 3.6; Conrad, *Reductive
group schemes* (2014), Corollary B.2.6 with Remark B.2.4). Let `S = Spec A`, let `J` be a
nilpotent ideal of `A` and `S₀ = Spec (A/J)`. Let `G` be a smooth `S`-group and `H` an
`S`-group of multiplicative type. Write `f₀` for the base change of a homomorphism `f : H ⟶ G`
to `S₀`.
1. Every homomorphism `u₀ : H_{S₀} ⟶ G_{S₀}` lifts to a homomorphism `u : H ⟶ G`.
2. Any two homomorphisms `u, u' : H ⟶ G` with `u₀ = u'₀` are conjugate under
   `ker(G(S) → G(S₀))`: there is `g ∈ G(S)` restricting to `1` in `G(S₀)` with
   `u' = int(g) ∘ u`. -/
def MultiplicativeTypeInfinitesimalLiftStatement : Prop :=
  ∀ (A : Type u) [CommRing A] (J : Ideal A), IsNilpotent J →
    ∀ (G H : GroupScheme (Spec (CommRingCat.of A))) [Smooth G.X.hom],
      RelativeMultiplicativeType.IsMultiplicativeType H →
        let r := Spec.algebraMap A (A ⧸ J)
        (∀ u₀ : (GroupScheme.baseChange r).obj H ⟶ (GroupScheme.baseChange r).obj G,
          ∃ u : H ⟶ G, (GroupScheme.baseChange r).map u = u₀) ∧
        (∀ u u' : H ⟶ G,
          (GroupScheme.baseChange r).map u = (GroupScheme.baseChange r).map u' →
          ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ G.X,
            G.constantPoint g (Over.mk r) = 1 ∧ u' = u ≫ (G.innerIso g).hom)

end Langlands.GroupScheme
