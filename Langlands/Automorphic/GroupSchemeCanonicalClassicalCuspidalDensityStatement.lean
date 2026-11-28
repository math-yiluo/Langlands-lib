import Langlands.Automorphic.GroupSchemeActualDifferential
import Langlands.Automorphic.GroupSchemeRestrictionCanonicalCuspidalL2
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # Classical cuspidal density on the canonical adelic quotient -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.Automorphic.GroupSchemeFunctions Langlands.GroupScheme
open InfiniteAdelicGroupPoints

/-- The closure of the square-integrable classical cuspidal image is the full
almost-everywhere cuspidal subspace of the canonical `L²([G])`. -/
def GroupSchemeCanonicalClassicalCuspidalDensityStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    (hK : Langlands.CompactIwasawa.IsMaximalCompact Kinf)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom),
    (canonicalCuspidalFormL2Image F G centralSplitTorusCharacter Kinf rho hsmooth
      (adelicDifferentialCommutator_of_smooth F G hsmooth) hPD hG hrho hK hN
    ).toSubmodule.topologicalClosure =
      canonicalFullAEL2CuspidalSubmodule F G centralSplitTorusCharacter hPD hG

end Langlands.Global.RestrictionSplitCentre
