import Langlands.GroupScheme.Rational.ClassFunctions
import Langlands.GroupScheme.Rational.QuasiSplitSteinbergQuotientStatement

/-! # Statement: rational lifting of strongly regular values of the canonical class quotient -/

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ClassFunctions

/-- A rational point of the actual canonical class-function quotient that becomes the image of
a point whose all-test centralizer lies in a closed torus, over some field, is the image of a
rational point of the group.
This is property 3 of `QuasiSplitSteinbergQuotientStatement` with its map fixed to
`ClassFunctions.rho G`; affineness is supplied by quasi-splitness. -/
def StronglyRegularRationalLiftingStatement : Prop :=
  ∀ (K : Type u) [Field K] (G : GroupScheme (Spec (CommRingCat.of K))),
    IsSimplyConnected G → ∀ hqs : IsQuasiSplit G,
    letI : IsAffineHom G.X.hom := hqs.isConnectedReductive.isAffineHom
    ∀ (v : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ ClassFunctions.quotient G)
      (F : Type u) [Field F] [Algebra K F]
      (w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G.X)
      (S : GroupScheme (Spec (CommRingCat.of F)))
      (j : S ⟶ (baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G),
      IsTorus S → IsClosedSubgroup j →
      (∀ {Z : Over (Spec (CommRingCat.of F))}
          (c : Z ⟶ ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G).X),
        c * (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm w) =
            (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm w) * c →
          ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c) →
      toUnit _ ≫ v = w ≫ ClassFunctions.rho G →
      ∃ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X, x ≫ ClassFunctions.rho G = v

end Langlands.GroupScheme.ClassFunctions
