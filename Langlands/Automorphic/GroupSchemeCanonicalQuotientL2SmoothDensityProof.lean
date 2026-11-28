import Langlands.Automorphic.GroupSchemeCanonicalQuotientL2SmoothDensityStatement
import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2SmoothDensityProof

/-! # Specialization of smooth-vector density to the canonical adelic quotient -/

set_option autoImplicit false

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme

/-- The canonical split components and Haar invariance supply the hypotheses
of the restriction split-centre density theorem. -/
theorem canonicalQuotientL2SmoothDensity : CanonicalQuotientL2SmoothDensityStatement := by
  intro F _ _ G _ _ hG
  let := canonical_finiteIndex F G hG
  let := AdelicGroupPoints.normOneHaarRightInvariant F G hG.smooth hG.connectedSpace
  let hs := isSplitComponent_canonicalComponent F G
  exact quotientL2SmoothDensity F G hG
    (canonicalRestrictionTorus F G) (canonicalRestrictionComponent F G)
    (canonicalTorus F G) (canonicalComponent F G) (canonicalSubgroup_eq_imageSubgroup F G)
    (canonical_characterRestrict_injective F G centralSplitTorusCharacter hG)
    hs.1.2 hs.1.1.1 (canonicalMeasure_rightInvariant F G centralSplitTorusCharacter hG)

end Langlands.Global.RestrictionSplitCentre
