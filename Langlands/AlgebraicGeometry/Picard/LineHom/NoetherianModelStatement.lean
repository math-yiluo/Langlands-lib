import Langlands.AlgebraicGeometry.CoherentSheaves.IntrinsicModuleHomPresheaf
import Langlands.AlgebraicGeometry.FiniteLinearModels
import Langlands.AlgebraicGeometry.Picard.LineBundle
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Noetherian affine-base finite linear models of line-bundle Hom -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.LineHom

/-- Over a noetherian affine base, the ordinary module Hom presheaf of two
locally free rank-one modules on a proper flat scheme is, naturally on the
entire slice, the solution presheaf of finitely many homogeneous linear
equations. -/
def NoetherianModelStatement : Prop :=
  ∀ (R : CommRingCat.{u}), IsNoetherianRing R →
    ∀ (Y : Scheme.{u}) (p : Y ⟶ Spec R), IsProper p → Flat p →
      ∀ (L M : Y.Modules), IsLocallyFreeRankOne L → IsLocallyFreeRankOne M →
        FiniteLinearEquations.HasModel
          (CoherentSheaves.intrinsicModuleHomPresheaf p L M)

end Langlands.AlgebraicGeometry.Picard.LineHom
