import Langlands.Automorphic.GroupSchemeInvariantForms
import Langlands.Automorphic.GroupSchemeRestrictionCanonicalCuspidalL2
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # Cuspidality of continuous representatives on the canonical quotient -/

noncomputable section

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.Automorphic.GroupSchemeFunctions Langlands.GroupScheme

/-- For a continuous representative invariant under the canonical split centre, full
cuspidality in `L²([G])` is equivalent to vanishing of all pointwise normalized periods. -/
def GroupSchemeCanonicalFullAEL2ContinuousCuspidalityStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
    (f : ContinuousRationalFunctions F G),
    IsLeftInvariantUnder F G (canonicalSubgroup F G) (evaluate F G f) →
    ∀ v : Lp ℂ 2 (canonicalMeasure F G),
    (v : CanonicalQuotient F G → ℂ) =ᵐ[canonicalMeasure F G]
      (fun y => evaluate F G f y.out) →
    (v ∈ canonicalFullAEL2CuspidalSubmodule F G centralSplitTorusCharacter hPD hG ↔
      f ∈ normalizedParabolicCuspidalSubrepresentation F G hPD hG)

end Langlands.Global.RestrictionSplitCentre
