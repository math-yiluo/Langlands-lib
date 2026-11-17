import Langlands.GroupScheme.Reductive.LocalSplitIsogenyRootDatumAdapter
import Langlands.GroupScheme.Reductive.LocalSplitRootDatumExistence

/-! # Local coordinate isogeny conjugacy without supplied root data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace Langlands.GroupScheme

/-- Local existence of torus conjugators for actual isogenies with closed
maximal coordinate tori. No fibrewise root data are supplied. -/
def LocalCoordinateIsogenyTorusConjugacyStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (G H : GroupScheme (Spec (CommRingCat.of R))), IsReductive G → IsReductive H →
    ∀ (I I' : Type u) [Fintype I] [Fintype I']
      (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
      (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H),
      IsClosedSubgroup i →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
      IsClosedSubgroup j →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j →
      ∀ (phi Phi : G ⟶ H), IsIsogeny phi → IsIsogeny Phi →
        (∃ tau : splitTorus (Spec (CommRingCat.of R)) I ⟶
          splitTorus (Spec (CommRingCat.of R)) I', i ≫ phi = tau ≫ j) →
        i ≫ phi = i ≫ Phi →
        FppfLocallyTorusConjugate (T := splitTorus.commGroupScheme _ I') j phi Phi

/-- The explicit intrinsic root-datum proposition implies coordinate
isogeny conjugacy over any local ring; root data are constructed internally. -/
theorem localCoordinateIsogenyTorusConjugacy_of_affineSplitSurjectionRootDatum
    (hAffine : AffineSplitSurjectionRootDatumStatement.{u}) :
    LocalCoordinateIsogenyTorusConjugacyStatement.{u} := by
  intro R _ _ G H hG hH I I' _ _ i j hi hmaxG hj hmaxH phi Phi hphi hPhi
    ht heq
  classical
  let := hG.isAffineHom
  let := hH.isAffineHom
  obtain ⟨J, P, hP⟩ := localSplitFibrewiseRootDatumExistence R G hG I i hi hmaxG
  obtain ⟨J', Q, hQ⟩ := localSplitFibrewiseRootDatumExistence R H hH I' j hj hmaxH
  let := hP.finite
  let := hP.isReduced
  let := hQ.finite
  let := hQ.isReduced
  let := hphi.1
  let := hPhi.1
  obtain ⟨tau, htau⟩ := ht
  exact RelativeIsogeny.fppfLocallyTorusConjugate_of_affineSplitSurjectionRootDatum
    i j hP hQ hG hH hi hj hmaxG hmaxH (Additive.ofMul tau) phi htau hAffine
    hphi.2.2 Phi (heq.symm.trans htau)

end Langlands.GroupScheme
