import Langlands.Representation.Plancherel.RationalSmoothCharacterModulus
import Langlands.Representation.Plancherel.RationalNormKernelCentralImage
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TemperedTwistIntegrability

/-! # Conditional unitary detection by the actual split-center point image -/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.RationalPoints
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

/-- The actual point image of a split component detects unitarity of smooth
complex characters, conditional on rational-character restriction injectivity
and all three actual local-point prerequisites. -/
def ConditionalRationalSplitCenterUnitaryDetectionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (M : GroupScheme (Spec (CommRingCat.of F))) (hM : GroupScheme.IsConnectedReductive M)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ M),
    GroupScheme.IsSplitComponent s →
    Function.Injective (GroupScheme.characterRestrict s) →
    CentralNormKernelCompactness M hM →
    CentralDerivedNormKernelCocompactness M hM →
    DerivedSmoothRealAnnihilation M hM →
    haveI : IsAffineHom M.X.hom := hM.isAffineHom
    haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
    letI : TopologicalSpace (GroupScheme.rationalPoints M) := rationalPointTopology F M.X
    Langlands.HarishChandraSchwartz.IsUnitaryDetecting
      (GroupScheme.rationalPoints.map s).range

end Langlands.Plancherel
