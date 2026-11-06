import Langlands.GroupScheme.CocharacterTransport
import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Torus.Lattice

/-! # Statement: a rational cross-section of the strongly regular classes -/

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **A rational cross-section of the strongly regular classes.** Let `G` be a simply
connected quasi-split group over a field `K`. Then there are a commutative `K`-algebra `A`
and a morphism `incl : Spec A ⟶ G` over `Spec K` with the following property. For every field
extension `E` of `K` and every point `y` of `G` with values in `E` whose all-test
centralizer in `G_E` lies in a closed `E`-torus, exactly one `E`-point `n` of `Spec A` has
`n ≫ incl` conjugate to `y` over some field extension of `E`. -/
def QuasiSplitStronglyRegularCrossSectionStatement : Prop :=
  ∀ (K : Type u) [Field K] (G : GroupScheme (Spec (CommRingCat.of K))),
    IsSimplyConnected G → IsQuasiSplit G →
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra K A)
      (incl : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A))) ⟶ G.X),
      ∀ (E : Type u) [Field E] [Algebra K E]
        (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶ G.X)
        (S : GroupScheme (Spec (CommRingCat.of E)))
        (j : S ⟶ (baseChange (Spec.map (CommRingCat.ofHom (algebraMap K E)))).obj G),
        IsTorus S → IsClosedSubgroup j →
        (∀ {Z : Over (Spec (CommRingCat.of E))}
            (c : Z ⟶ ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K E)))).obj G).X),
          c * (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm y) =
              (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm y) * c →
            ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c) →
        ∃! n : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A))),
          ∃ (E' : Type u) (_ : Field E') (_ : Algebra K E')
            (q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E'))) ⟶
              Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))))
            (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E'))) ⟶ G.X),
            g * (q ≫ n ≫ incl) * g⁻¹ = q ≫ y

end Langlands.GroupScheme
