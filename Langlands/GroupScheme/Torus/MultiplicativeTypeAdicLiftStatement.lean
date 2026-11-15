import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.InnerAutomorphism
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.AdicCompletion.Basic

/-! # Statement: lifting homomorphisms from isotrivial groups of multiplicative type over adically complete noetherian rings -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeMultiplicativeType

/-- SGA 3, Exposé IX, Corollaire 7.3. Let `A` be a noetherian ring, separated and complete for
the `I`-adic topology of an ideal `I`, let `S = Spec A` and `S₀ = Spec (A / I)`. Let `H` be an
`S`-group that becomes diagonalizable over a finite étale surjective `S' ⟶ S`, and let `G` be a
smooth affine `S`-group. Write `u₀ = u_{S₀}` for the reduction of a homomorphism `u : H ⟶ G`.
1. Every homomorphism `u₀ : H_{S₀} ⟶ G_{S₀}` of `S₀`-groups lifts to a homomorphism
   `u : H ⟶ G` of `S`-groups.
2. Any two lifts `u, u'` of the same homomorphism are conjugate by a point `g ∈ G(S)` reducing to
   the unit of `G(S₀)`: `u' = int(g) ∘ u`. -/
def MultiplicativeTypeAdicLiftStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (H G : GroupScheme (Spec (CommRingCat.of A))) [Smooth G.X.hom] [IsAffineHom G.X.hom],
    (∃ (S' : Scheme.{u}) (p : S' ⟶ Spec (CommRingCat.of A)),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
        IsDiagonalizable ((GroupScheme.baseChange p).obj H)) →
      let r := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (∀ u₀ : (GroupScheme.baseChange r).obj H ⟶ (GroupScheme.baseChange r).obj G,
        ∃ u : H ⟶ G, (GroupScheme.baseChange r).map u = u₀) ∧
      (∀ u u' : H ⟶ G,
        (GroupScheme.baseChange r).map u = (GroupScheme.baseChange r).map u' →
        ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ G.X,
          G.constantPoint g (Over.mk r) = 1 ∧ u' = u ≫ (G.innerIso g).hom)

end Langlands.GroupScheme
