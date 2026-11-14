import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.InnerAutomorphism
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Statement: lifting subgroups of multiplicative type through nilpotent thickenings -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeMultiplicativeType in
/-- **Infinitesimal lifting of subgroups of multiplicative type** (SGA 3, IX, Théorème 3.6 bis,
with Corollaire 3.3 bis). Let `S = Spec A`, let `J` be a nilpotent ideal of `A`,
`S₀ = Spec (A/J)`, and let `G` be a smooth `S`-group with base change `G₀` to `S₀`. Subgroups
are given by homomorphisms whose underlying morphism of schemes is an immersion; two of them
are equal when they have the same functor of points (`SubgroupFunctor.range`).
1. (a) For every subgroup `H₀` of `G₀` of multiplicative type there is a subgroup `H` of `G`,
   flat over `S`, with `H ×_S S₀ = H₀`.
2. (b) Every subgroup `H` of `G`, flat over `S`, whose base change to `S₀` is of
   multiplicative type, is of multiplicative type.
3. (c) If `H, H'` are subgroups of `G`, flat over `S`, with equal base changes to `S₀` of
   multiplicative type, then `H' = int(g)(H)` for some `g ∈ G(S)` reducing to the unit of
   `G(S₀)`. -/
def MultiplicativeTypeSubgroupInfinitesimalLiftStatement : Prop :=
  ∀ (A : Type u) [CommRing A] (J : Ideal A), IsNilpotent J →
    ∀ (G : GroupScheme (Spec (CommRingCat.of A))) [Smooth G.X.hom],
      let r := Spec.algebraMap A (A ⧸ J)
      (∀ (H₀ : GroupScheme (Spec (CommRingCat.of (A ⧸ J))))
          (h₀ : H₀ ⟶ (GroupScheme.baseChange r).obj G),
          IsImmersion h₀.hom.hom.left → IsMultiplicativeType H₀ →
          ∃ (H : GroupScheme (Spec (CommRingCat.of A))) (h : H ⟶ G),
            IsImmersion h.hom.hom.left ∧ Flat H.X.hom ∧
              SubgroupFunctor.range ((GroupScheme.baseChange r).map h) =
                SubgroupFunctor.range h₀) ∧
      (∀ (H : GroupScheme (Spec (CommRingCat.of A))) (h : H ⟶ G),
          IsImmersion h.hom.hom.left → Flat H.X.hom →
          IsMultiplicativeType ((GroupScheme.baseChange r).obj H) → IsMultiplicativeType H) ∧
      (∀ (H H' : GroupScheme (Spec (CommRingCat.of A))) (h : H ⟶ G) (h' : H' ⟶ G),
          IsImmersion h.hom.hom.left → Flat H.X.hom →
          IsImmersion h'.hom.hom.left → Flat H'.X.hom →
          IsMultiplicativeType ((GroupScheme.baseChange r).obj H) →
          SubgroupFunctor.range ((GroupScheme.baseChange r).map h) =
            SubgroupFunctor.range ((GroupScheme.baseChange r).map h') →
          ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ G.X,
            G.constantPoint g (Over.mk r) = 1 ∧
              SubgroupFunctor.range (h ≫ (G.innerIso g).hom) = SubgroupFunctor.range h')

end Langlands.GroupScheme
