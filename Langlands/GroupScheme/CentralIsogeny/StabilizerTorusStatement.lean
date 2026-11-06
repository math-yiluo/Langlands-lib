import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: stabilizers of torus-centralized points under central isogenies -/

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Stabilizer tori through central isogenies.** Let `π : G ⟶ A` be a central isogeny of
group schemes over a field `K` and `a` an action of `A` on `G` with `a(π h) g = h g h⁻¹`.
If a rational point `x` of `G` has all-test centralizer inside a closed torus of `G`, then
there is a closed torus `j : S ⟶ A` through which every point of `A` on any test fixing `x`
under `a` factors. -/
def CentralIsogenyStabilizerTorusStatement : Prop :=
  ∀ (K : Type u) [Field K] (G A : GroupScheme (Spec (CommRingCat.of K))) (π : G ⟶ A),
    IsCentralIsogeny π →
    ∀ (a : AutomorphicAction A G),
      (∀ {Z : Over (Spec (CommRingCat.of K))} (h g : Z ⟶ G.X),
        a.act (h ≫ π.hom.hom) g = h * g * h⁻¹) →
    ∀ (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X)
      (T : GroupScheme (Spec (CommRingCat.of K))) (i : T ⟶ G),
      IsTorus T → IsClosedSubgroup i →
      (∀ {Z : Over (Spec (CommRingCat.of K))} (c : Z ⟶ G.X),
        c * (toUnit Z ≫ x) = (toUnit Z ≫ x) * c → ∃ t : Z ⟶ T.X, t ≫ i.hom.hom = c) →
      ∃ (S : GroupScheme (Spec (CommRingCat.of K))) (j : S ⟶ A),
        IsTorus S ∧ IsClosedSubgroup j ∧
          ∀ {Z : Over (Spec (CommRingCat.of K))} (c : Z ⟶ A.X),
            a.act c (toUnit Z ≫ x) = toUnit Z ≫ x → ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c

end Langlands.GroupScheme
