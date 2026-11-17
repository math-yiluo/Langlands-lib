import Langlands.GroupScheme.HomScheme.InfinitesimalReduction
import Langlands.GroupScheme.HomScheme.SquareZeroCohomologyStatement
import Langlands.GroupScheme.Cohomology.MultiplicativeTypeVanishingStatement

/-! # Assembly of infinitesimal lifting from cohomology and source geometry -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.HomScheme

/-- The exact target follows from low-degree multiplicative-type cohomology
vanishing, the square-zero deformation bridge, and the flat affine geometry of
multiplicative-type sources. All four prerequisites remain explicit inputs. -/
theorem multiplicativeTypeInfinitesimalLift_of_cohomology
    (hcoh : Cohomology.MultiplicativeTypeLowDegreeVanishingStatement.{u})
    (hdeform : SquareZeroHomomorphismCohomologyStatement.{u})
    (hflat : ∀ (S : Scheme.{u}) (H : GroupScheme S),
      RelativeMultiplicativeType.IsMultiplicativeType H → Flat H.X.hom)
    (haff : ∀ (S : Scheme.{u}) (H : GroupScheme S),
      RelativeMultiplicativeType.IsMultiplicativeType H → IsAffineHom H.X.hom) :
    MultiplicativeTypeInfinitesimalLiftStatement.{u} := by
  apply multiplicativeTypeInfinitesimalLift_of_squareZero
  intro S H G _ hH A _ I hI a b w
  have hHa := hH.baseChange a
  let : IsAffineHom ((baseChange a).obj H).X.hom := haff _ _ hHa
  exact hdeform S H G A I hI a b w (hflat _ _ hHa)
    (isAffine_of_isAffineHom ((baseChange a).obj H).X.hom)
    (hcoh _ _ (hH.baseChange b))

end Langlands.GroupScheme.HomScheme
