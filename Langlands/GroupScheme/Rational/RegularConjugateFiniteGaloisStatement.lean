import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.CocharacterTransport
import Mathlib.FieldTheory.Galois.Basic

/-! # Statement: finite Galois conjugacy to a point with toral centralizer -/

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Finite Galois conjugacy to a point with toral centralizer.** Let `G` be a connected
reductive group over a field `K`, `L/K` a finite Galois extension and `z` a point of `G` over
`Spec L` whose all-test centralizer in `G_L` lies in a closed torus `S` of `G_L`. If a rational
point `x` of `G` becomes conjugate to `z` over some field extension `E` of `K` through a
morphism of covers `q` from `Spec E` to `Spec L`, then the all-test centralizer of `x` lies in a
closed torus of `G`, and `x` is already conjugate to `z` over a finite Galois extension `L'/K`
through a morphism of covers `r` from `Spec L'` to `Spec L`. -/
def RegularConjugateFiniteGaloisStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (G : GroupScheme (Spec (CommRingCat.of K))), IsConnectedReductive G →
    ∀ (z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ G.X)
      (S : GroupScheme (Spec (CommRingCat.of L)))
      (j : S ⟶ (baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj G),
      IsTorus S → IsClosedSubgroup j →
      (∀ {Z : Over (Spec (CommRingCat.of L))}
        (c : Z ⟶ ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj G).X),
        c * (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm z) =
          (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm z) * c →
        ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c) →
    ∀ (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X)
      (E : Type u) [Field E] [Algebra K E]
      (q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶ G.X),
      g * (toUnit _ ≫ x) * g⁻¹ = q ≫ z →
      ∃ (T : GroupScheme (Spec (CommRingCat.of K))) (i : T ⟶ G),
        IsTorus T ∧ IsClosedSubgroup i ∧
        (∀ {Z : Over (Spec (CommRingCat.of K))} (c : Z ⟶ G.X),
          c * (toUnit Z ≫ x) = (toUnit Z ≫ x) * c → ∃ t : Z ⟶ T.X, t ≫ i.hom.hom = c) ∧
        ∃ (L' : Type u) (_ : Field L') (_ : Algebra K L')
          (_ : FiniteDimensional K L') (_ : IsGalois K L')
          (r : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L'))) ⟶
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))
          (g' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L'))) ⟶ G.X),
          g' * (toUnit _ ≫ x) * g'⁻¹ = r ≫ z

end Langlands.GroupScheme
