import Langlands.Geometry.EtaleInverseImage
import Langlands.Geometry.EtalePullbackAdjunction
import Langlands.Geometry.EtaleRestrictionRightAdjoint

/-! # Comparing constructed inverse image with etale restriction -/

noncomputable section

universe u uA vA

namespace Langlands.Geometry.EtaleInverseImage

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X) [Etale f]
  (A : Type uA) [Category.{vA} A]

/-- The actual composition/base-change adjunction on etale objects induces
the adjunction between existing restriction and geometric direct image. -/
def restrictionGeometricAdjunction :
    EtalePullback.restriction f A ⊣ EtaleDirectImage.directImage f A :=
  (EtalePullback.siteMapPullbackAdjunction f).sheafPushforwardContinuous (E := A)
    Z.smallEtaleTopology X.smallEtaleTopology

/-- The previous right-Kan direct image identifies canonically with actual
evaluation on geometric base change. -/
def rightKanDirectImageIsoGeometric :
    EtalePullback.directImage f A ≅ EtaleDirectImage.directImage f A :=
  Adjunction.rightAdjointUniq (EtalePullback.restrictionAdjunction f A)
    (restrictionGeometricAdjunction f A)

variable (R : Type u) [CommRing R]

/-- For an etale base map, the constructed arbitrary-morphism inverse image
identifies with the existing restriction functor. -/
def inverseImageIsoRestriction :
    inverseImage f R ≅ EtalePullback.restriction f (ModuleCat.{u} R) :=
  Adjunction.leftAdjointUniq (inverseImageAdjunction f R)
    (restrictionGeometricAdjunction f (ModuleCat.{u} R))

/-- Along an etale map, the constructed inverse image preserves finite limits,
by the actual restriction comparison. -/
instance inverseImage_etale_preservesFiniteLimits :
    PreservesFiniteLimits (inverseImage f R) :=
  preservesFiniteLimits_of_natIso (inverseImageIsoRestriction f R).symm

end Langlands.Geometry.EtaleInverseImage
