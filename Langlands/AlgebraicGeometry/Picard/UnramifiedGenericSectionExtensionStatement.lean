import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Langlands.AlgebraicGeometry.Picard.ClosedIrreducibleImages
import Langlands.AlgebraicGeometry.Picard.GenericSectionRestriction
import Langlands.AlgebraicGeometry.Picard.GeometricallyUnibranchDomain
import Langlands.AlgebraicGeometry.Picard.ValuationBaseNormality

/-! # Extension of generic sections of unramified morphisms -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- The integral, geometrically unibranch specialization of the final
assertion of EGA IV 18.10.19, expressed on actual generic residue-field maps.
This defines the proposition; it does not prove section existence. -/
def UnramifiedGenericSectionExtensionStatement : Prop :=
  ∀ (S X : Scheme.{u}) [IsIntegral S],
    GeometricallyUnibranchIntegralScheme S →
    ∀ (p : X ⟶ S) [IsSeparated p] [LocallyOfFiniteType p] [FormallyUnramified p],
      ClosedIrreducibleImages p →
      Function.Surjective (genericSectionRestriction p)

/-- Normality of the actual stalks supplies the scheme hypothesis
in the generic-section extension proposition. -/
theorem geometricallyUnibranchIntegralScheme_of_hasNormalStalks
    (S : Scheme.{u}) [IsIntegral S] (hS : HasNormalStalks S) :
    GeometricallyUnibranchIntegralScheme S :=
  geometricallyUnibranchIntegralScheme_of_stalks S (fun x => (hS x).2)

/-- Valuation spectra satisfy the base hypothesis without a rank or
noetherianity restriction; fields are included. -/
theorem valuation_spec_geometricallyUnibranch
    (R : CommRingCat.{u}) [IsDomain R] [ValuationRing R] :
    GeometricallyUnibranchIntegralScheme (Spec R) :=
  geometricallyUnibranchIntegralScheme_of_hasNormalStalks (Spec R)
    (valuation_spec_hasNormalStalks R)

end Langlands.AlgebraicGeometry
