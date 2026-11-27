import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.AdelicLocalFinitenessStatement

/-! # Levi restrictions of radical averages of adelic test functions -/

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-- Radical averages of test functions restrict to test functions on the Levi. -/
def LeviRadicalAverageTestFunctionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
    (β : AdelicGroupPoints F G → ℂ), IsAdelicTestFunction F G β →
    haveI : IsClosed (AdelicSubgroupPoints.adelicPoints F G
        (SubgroupFunctor.range (fam.iU J ≫ fam.p J)) : Set (AdelicGroupPoints F G)) :=
      AdelicSubgroupPoints.isClosed_adelicPoints_range F G (fam.iU J ≫ fam.p J)
    IsAdelicTestFunction F (fam.M J) fun m =>
      ∫ u : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (fam.iU J ≫ fam.p J)),
        β ((u : AdelicGroupPoints F G) * map F (fam.M J) G (fam.l J ≫ fam.p J) m)
        ∂AdelicSubgroupPoints.normalizedHaarMeasure F G
          (SubgroupFunctor.range (fam.iU J ≫ fam.p J))

end Langlands.Global
