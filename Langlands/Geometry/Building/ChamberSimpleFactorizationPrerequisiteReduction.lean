import Langlands.Geometry.Building.AffineIwahoriTitsInputStatements
import Langlands.Geometry.Building.ChamberSimpleParahoricFactorization
import Langlands.GroupScheme.Rational.DynamicRootProductRayReduction
import Langlands.GroupScheme.Rational.RootRayFromFactorPairs

/-! # Algebraic prerequisites for the exact chamber-simple factorization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- The exact chamber-simple target follows from rank-one factorization and
the cover-image comparison for the actual zero data, without a separate
Dynamic ordered-product premise. -/
def ChamberSimpleFactorizationPrerequisiteReductionStatement : Prop :=
  RootRankOneFactorizationStatement.{u} →
  (∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G),
      P.zeroDatum.CoverImageCentralizerNormKernelStatement) →
  ChamberSimpleFactorizationStatement.{u}

/-- The existing ray and Dynamic product reductions supply all product inputs
to the published local chamber-simple factorization. -/
theorem chamberSimpleFactorizationPrerequisiteReduction :
    ChamberSimpleFactorizationPrerequisiteReductionStatement.{u} := by
  intro hrank hZ
  have hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u} :=
    RelativeRoot.dynamicRootOrderedProduct_of_rayDecomposition
      (RelativeRoot.relativeRootRayDecompositionStatement_of_rootRankOneFactorizationStatement
        hrank)
  intro F _ _ _ _ G _ P hA C hC ψ hψ alpha hwall v hv g hg
  exact P.simpleFactorization_of_rankOneFactorization hA
    (hrank F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus)
    (hZ F G P) hprod hψ hwall hv hg

/-- The minimal-Levi zero comparison supplies the cover-image input, keeping
every supplied zero datum and the original target's apartment hypotheses. -/
theorem chamberSimpleFactorizationStatement_of_minimalLeviZeroComparison
    (hrank : RootRankOneFactorizationStatement.{u})
    (hzero : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
      (P : ParahoricBuildingData G),
        P.zeroDatum.MinimalLeviZeroComparisonStatement) :
    ChamberSimpleFactorizationStatement.{u} := by
  apply chamberSimpleFactorizationPrerequisiteReduction hrank
  intro F _ _ _ _ G _ P
  exact P.zeroDatum.coverImageCentralizerNormKernel_of_intersection (hzero F G P).2

end Langlands.Geometry.Building
