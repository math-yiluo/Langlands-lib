import Langlands.Geometry.EtaleInverseImage
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Linear structure on the constructed etale inverse-image adjunction -/

noncomputable section

universe u

namespace Langlands.Geometry.EtaleInverseImage

open CategoryTheory AlgebraicGeometry
open EtaleDirectImage

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X) (R : Type u) [CommRing R]

/-- The constructed inverse image is additive because its actual right
adjoint is additive. -/
instance inverseImage_additive : (inverseImage f R).Additive :=
  (inverseImageAdjunction f R).left_adjoint_additive

/-- The actual adjunction transports coefficient scalar multiplication
from geometric direct image to constructed inverse image. -/
instance inverseImage_linear : (inverseImage f R).Linear R where
  map_smul a r := ((inverseImageAdjunction f R).homEquiv _ _).injective (by
    simp [Adjunction.homEquiv_unit])

/-- The actual inverse/direct-image Hom correspondence is an R-linear
equivalence on the original module-sheaf morphisms. -/
def homLinearEquiv
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u} R)) :
    ((inverseImage f R).obj F ⟶ G) ≃ₗ[R]
      (F ⟶ (directImage f (ModuleCat.{u} R)).obj G) :=
  { (inverseImageAdjunction f R).homAddEquiv F G with
    map_smul' := by
      intro r a
      simp [Adjunction.homEquiv_unit] }

@[simp] theorem homLinearEquiv_apply
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u} R))
    (a : (inverseImage f R).obj F ⟶ G) :
    homLinearEquiv f R F G a =
      (inverseImageAdjunction f R).unit.app F ≫
        (directImage f (ModuleCat.{u} R)).map a :=
  (inverseImageAdjunction f R).homEquiv_unit F G a

@[simp] theorem homLinearEquiv_symm_apply
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u} R))
    (a : F ⟶ (directImage f (ModuleCat.{u} R)).obj G) :
    (homLinearEquiv f R F G).symm a =
      (inverseImage f R).map a ≫ (inverseImageAdjunction f R).counit.app G :=
  (inverseImageAdjunction f R).homEquiv_counit F G a

end Langlands.Geometry.EtaleInverseImage
