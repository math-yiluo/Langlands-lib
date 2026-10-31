import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsRepresentative
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Noetherian.Basic

/-! # Universal perfect sections over a noetherian base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

attribute [local instance] HasDerivedCategory.standard

/-- A smooth proper line bundle over a noetherian affine base has one
strictly perfect representative computing all affine scalar changes. -/
def NoetherianUniversalPerfectSectionsStatement : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R]
    (X : Scheme.{u}) (f : X ⟶ Spec R),
    Smooth f → IsProper f →
    ∀ L : Picard.LineBundle X,
      ∃ K : CochainComplex (ModuleCat.{u} R) ℤ,
        IsUniversalPerfectSectionsRepresentative f L.obj K

end Langlands.AlgebraicGeometry.Modules
