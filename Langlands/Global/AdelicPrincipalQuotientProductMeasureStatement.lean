import Langlands.Global.AdelicPrincipalQuotientProduct

/-! # Exact product measure on the full principal adelic quotient -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme AdelicGroupPoints

/-- The full principal quotient carries the product of the normalized positive central Haar
measure and the existing measure on the canonical split-centre quotient. -/
def PrincipalQuotientProductMeasureStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G),
    MeasurePreserving (principalQuotientProductEquiv F G hG)
      (rationalQuotientHaarMeasure F G)
      ((positiveCentreHaarMeasure F G hG).prod (canonicalMeasure F G))

end Langlands.Global.RestrictionSplitCentre
