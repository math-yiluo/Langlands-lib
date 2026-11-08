import Langlands.Shimura.Coefficients.EtaleInverseImageConstantProduct
import Langlands.Shimura.Coefficients.EtaleProductPullbackCoherence
import Langlands.Geometry.EtaleInverseImageRestrictionCoherence

/-! # Identity normalization of geometric inverse-image product coordinates -/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Geometry Langlands.Geometry.EtaleInverseImage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme.{u}} (R : Type u) [CommRing R]

/-- Identity base change of a product sheaf retains the actual pullback cover
comparison and the canonical inverse-image identity on coefficients. -/
@[reassoc] theorem inverseImageProductSheafMap_id (V : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    inverseImageProductSheafMap (𝟙 X) R V F ≫
        (productSheaf X.smallEtaleTopology ((etaleObjectPullback (𝟙 X)).obj V)).map
          ((inverseImageId R X).hom.app F) =
      (inverseImageId R X).hom.app ((productSheaf X.smallEtaleTopology V).obj F) ≫
        coverPullback X.smallEtaleTopology ((etaleObjectPullbackId X).hom.app V) F := by
  have h (H : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
      (inverseImageIsoRestriction (𝟙 X) R).hom.app H ≫
          (EtalePullback.restrictionId (ModuleCat.{u} R)).hom.app H =
        (inverseImageId R X).hom.app H :=
    congrArg (fun t => t.app H) (inverseImageIsoRestriction_id R X)
  have e :
      (inverseImageIsoRestriction (𝟙 X) R).inv.app F ≫
          (inverseImageId R X).hom.app F =
        (EtalePullback.restrictionId (ModuleCat.{u} R)).hom.app F := by
    rw [← h F, Iso.inv_hom_id_app_assoc]
  rw [inverseImageProductSheafMap_etale, Category.assoc, Category.assoc,
    ← Functor.map_comp, e, etaleProductSheafPullback_id, ← Category.assoc, h]

/-- The normalized identity product map uses both the coefficient identity
comparison and the actual inverse cover comparison. -/
def inverseImageProductIdentityMap (V : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (inverseImage (𝟙 X) R).obj ((productSheaf X.smallEtaleTopology V).obj F) ⟶
      (productSheaf X.smallEtaleTopology V).obj F :=
  inverseImageProductSheafMap (𝟙 X) R V F ≫
    (productSheaf X.smallEtaleTopology ((etaleObjectPullback (𝟙 X)).obj V)).map
      ((inverseImageId R X).hom.app F) ≫
    coverPullback X.smallEtaleTopology ((etaleObjectPullbackId X).inv.app V) F

/-- Normalization recovers the actual inverse-image identity of the product sheaf. -/
theorem inverseImageProductIdentityMap_eq (V : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    inverseImageProductIdentityMap R V F =
      (inverseImageId R X).hom.app ((productSheaf X.smallEtaleTopology V).obj F) := by
  dsimp only [inverseImageProductIdentityMap]
  rw [inverseImageProductSheafMap_id_assoc, ← coverPullback_comp,
    Iso.inv_hom_id_app]
  change (inverseImageId R X).hom.app ((productSheaf X.smallEtaleTopology V).obj F) ≫
      coverPullback X.smallEtaleTopology (𝟙 V) F = _
  rw [coverPullback_id]
  exact Category.comp_id _

/-- The normalized product identity is natural in every coefficient sheaf. -/
@[reassoc] theorem inverseImageProductIdentityMap_natural (V : X.Etale)
    {F F' : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (a : F ⟶ F') :
    (inverseImage (𝟙 X) R).map ((productSheaf X.smallEtaleTopology V).map a) ≫
        inverseImageProductIdentityMap R V F' =
      inverseImageProductIdentityMap R V F ≫
        (productSheaf X.smallEtaleTopology V).map a := by
  rw [inverseImageProductIdentityMap_eq, inverseImageProductIdentityMap_eq]
  exact (inverseImageId R X).hom.naturality _

/-- Constant product coordinates along the identity have the actual geometric
identity comparison after restriction along the inverse cover comparison. -/
@[reassoc] theorem inverseImageConstantProductMap_id (V : X.Etale) (M : ModuleCat.{u} R) :
    inverseImageConstantProductMap (𝟙 X) R V M ≫
        coverPullback X.smallEtaleTopology ((etaleObjectPullbackId X).inv.app V)
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M) =
      (inverseImageId R X).hom.app
        ((productSheaf X.smallEtaleTopology V).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M)) := by
  dsimp only [inverseImageConstantProductMap]
  rw [inverseImageConstantIso_id, Category.assoc]
  exact inverseImageProductIdentityMap_eq R V _

end Langlands.Shimura.Coefficients
