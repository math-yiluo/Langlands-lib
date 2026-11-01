import Langlands.Geometry.EtaleDirectImage
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-! # Constructed inverse image for module sheaves on small etale sites -/

noncomputable section

universe u

namespace Langlands.Geometry.EtaleInverseImage

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Shimura.Coefficients EtaleDirectImage

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X)

/-- Geometric base change restricted to the essentially-small affine etale
source site. The target objects need not be affine. -/
abbrev affineSiteMap : X.AffineEtale ⥤ Z.Etale :=
  Scheme.AffineEtale.Spec X ⋙ etaleObjectPullback f

instance affineSiteMap_isContinuous :
    (affineSiteMap f).IsContinuous (Scheme.AffineEtale.topology X)
      Z.smallEtaleTopology :=
  Functor.isContinuous_comp (Scheme.AffineEtale.Spec X) (etaleObjectPullback f)
    (Scheme.AffineEtale.topology X) X.smallEtaleTopology Z.smallEtaleTopology

variable (R : Type u) [CommRing R]

/-- Essential smallness of the affine source supplies each actual comma
colimit in the original module universe. -/
instance affineSiteMap_hasPointwiseLeftKanExtension
    (F : X.AffineEtaleᵒᵖ ⥤ ModuleCat.{u} R) :
    (affineSiteMap f).op.HasPointwiseLeftKanExtension F := by
  intro V
  have : HasColimitsOfShape (CostructuredArrow (affineSiteMap f).op V)
      (ModuleCat.{u} R) :=
    HasColimitsOfShape.of_essentiallySmall.{u, u}
      (ModuleCat.{u} R) (CostructuredArrow (affineSiteMap f).op V)
  infer_instance

/-- Left Kan extension along actual base change, followed by sheafification
on the target small etale site. -/
def affineInverseImage :
    Sheaf (Scheme.AffineEtale.topology X) (ModuleCat.{u} R) ⥤
      Sheaf Z.smallEtaleTopology (ModuleCat.{u} R) :=
  Functor.sheafPullbackConstruction.sheafPullback (affineSiteMap f) (ModuleCat.{u} R)
    (Scheme.AffineEtale.topology X) Z.smallEtaleTopology

/-- The Kan-extension/sheafification adjunction on the affine source site. -/
def affineAdjunction :
    affineInverseImage f R ⊣
      (affineSiteMap f).sheafPushforwardContinuous (ModuleCat.{u} R)
        (Scheme.AffineEtale.topology X) Z.smallEtaleTopology :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (affineSiteMap f) (ModuleCat.{u} R)
    (Scheme.AffineEtale.topology X) Z.smallEtaleTopology

/-- Restrict to the affine etale site, then apply the constructed Kan extension
and target sheafification. -/
def inverseImage :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} R) ⥤
      Sheaf Z.smallEtaleTopology (ModuleCat.{u} R) :=
  (Scheme.AffineEtale.sheafEquiv X (ModuleCat.{u} R)).inverse ⋙
    affineInverseImage f R

/-- Affine restriction of direct image, transported back across the dense-site
equivalence, is the original geometric direct image. -/
def directImageFromAffineIso :
    (affineSiteMap f).sheafPushforwardContinuous (ModuleCat.{u} R)
        (Scheme.AffineEtale.topology X) Z.smallEtaleTopology ⋙
      (Scheme.AffineEtale.sheafEquiv X (ModuleCat.{u} R)).functor ≅
    directImage f (ModuleCat.{u} R) :=
  Functor.associator (directImage f (ModuleCat.{u} R))
      (Scheme.AffineEtale.sheafEquiv X (ModuleCat.{u} R)).inverse
      (Scheme.AffineEtale.sheafEquiv X (ModuleCat.{u} R)).functor ≪≫
    Functor.isoWhiskerLeft (directImage f (ModuleCat.{u} R))
      (Scheme.AffineEtale.sheafEquiv X (ModuleCat.{u} R)).counitIso ≪≫
    (directImage f (ModuleCat.{u} R)).rightUnitor

/-- The constructed inverse image is left adjoint to actual arbitrary-morphism
direct image. No inverse-image functor or adjunction is an input. -/
def inverseImageAdjunction :
    inverseImage f R ⊣ directImage f (ModuleCat.{u} R) :=
  (((Scheme.AffineEtale.sheafEquiv X (ModuleCat.{u} R)).symm.toAdjunction).comp
    (affineAdjunction f R)).ofNatIsoRight (directImageFromAffineIso f R)

instance inverseImage_isLeftAdjoint : (inverseImage f R).IsLeftAdjoint :=
  (inverseImageAdjunction f R).isLeftAdjoint

instance directImage_isRightAdjoint :
    (directImage f (ModuleCat.{u} R)).IsRightAdjoint :=
  (inverseImageAdjunction f R).isRightAdjoint

end Langlands.Geometry.EtaleInverseImage
