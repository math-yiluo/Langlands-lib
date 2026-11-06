import Langlands.GroupScheme.Rational.ClassFunctions
import Langlands.GroupScheme.Rational.QuasiSplitSteinbergQuotientStatement

/-! # Statement: strongly regular fibres of the canonical class-function quotient -/

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ClassFunctions

/-- Geometric conjugacy in a fibre of the actual canonical class-function quotient
through a point whose all-test centralizer lies in a closed torus.
This is property 2 of `QuasiSplitSteinbergQuotientStatement` with its map fixed to
`ClassFunctions.rho G`; affineness is supplied by quasi-splitness.
No additional regularity or semisimplicity is assumed of `y`. -/
def StronglyRegularFibresStatement : Prop :=
  ∀ (K : Type u) [Field K] (G : GroupScheme (Spec (CommRingCat.of K))),
    IsSimplyConnected G → ∀ hqs : IsQuasiSplit G,
    letI : IsAffineHom G.X.hom := hqs.isConnectedReductive.isAffineHom
    ∀ (F : Type u) [Field F] [Algebra K F]
      (y w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G.X)
      (S : GroupScheme (Spec (CommRingCat.of F)))
      (j : S ⟶ (baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G),
      IsTorus S → IsClosedSubgroup j →
      (∀ {Z : Over (Spec (CommRingCat.of F))}
          (c : Z ⟶ ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G).X),
        c * (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm w) =
            (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm w) * c →
          ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c) →
      y ≫ ClassFunctions.rho G = w ≫ ClassFunctions.rho G →
      ∃ (E : Type u) (_ : Field E) (_ : Algebra K E)
        (q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))))
        (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶ G.X),
        g * (q ≫ y) * g⁻¹ = q ≫ w

end Langlands.GroupScheme.ClassFunctions
