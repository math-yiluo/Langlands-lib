import Langlands.Geometry.EtaleImageFunctoriality
import Langlands.Geometry.EtaleScalarExtension

/-! # Arbitrary geometric inverse image and coefficient scalar extension -/

noncomputable section

universe u

namespace Langlands.Geometry.EtaleInverseImage

open CategoryTheory AlgebraicGeometry
open EtaleDirectImage EtaleCohomologyAction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
variable {X Z : Scheme.{u}} (f : Z ⟶ X)

/-- Geometric direct image and restriction of coefficient scalars have the
same sectionwise data for every scheme map. -/
def directImageRestrictScalarsIso :
    directImage f (ModuleCat.{u} S) ⋙ sheafRestrictScalars φ X ≅
      sheafRestrictScalars φ Z ⋙ directImage f (ModuleCat.{u} R) :=
  Iso.refl _

/-- Scalar restriction preserves the actual identity direct-image comparison. -/
theorem directImageId_restrictScalars (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} S)) :
    (directImageId (ModuleCat.{u} R) X).hom.app ((sheafRestrictScalars φ X).obj F) =
      (sheafRestrictScalars φ X).map ((directImageId (ModuleCat.{u} S) X).hom.app F) := by
  apply Sheaf.hom_ext
  rfl

/-- Scalar restriction preserves the actual composition direct-image comparison. -/
theorem directImageComp_restrictScalars {V : Scheme.{u}} (g : V ⟶ Z)
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u} S)) :
    (directImageComp (ModuleCat.{u} R) f g).hom.app
        ((sheafRestrictScalars φ V).obj F) =
      (sheafRestrictScalars φ X).map
        ((directImageComp (ModuleCat.{u} S) f g).hom.app F) := by
  apply Sheaf.hom_ext
  rfl

/-- Extension then inverse image is adjoint to scalar restriction then
geometric direct image, by the actual strict right-adjoint interchange. -/
def extendScalarsInverseImageAdjunction :
    sheafExtendScalars φ X ⋙ inverseImage f S ⊣
      sheafRestrictScalars φ Z ⋙ directImage f (ModuleCat.{u} R) :=
  ((sheafExtendRestrictScalarsAdj φ X).comp (inverseImageAdjunction f S)).ofNatIsoRight
    (directImageRestrictScalarsIso φ f)

/-- Inverse image then extension has the same actual right adjoint. -/
def inverseImageExtendScalarsAdjunction :
    inverseImage f R ⋙ sheafExtendScalars φ Z ⊣
      sheafRestrictScalars φ Z ⋙ directImage f (ModuleCat.{u} R) :=
  (inverseImageAdjunction f R).comp (sheafExtendRestrictScalarsAdj φ Z)

/-- Actual arbitrary-morphism inverse image commutes naturally with
sheafified extension of coefficient scalars. -/
def inverseImageExtendScalarsIso :
    sheafExtendScalars φ X ⋙ inverseImage f S ≅
      inverseImage f R ⋙ sheafExtendScalars φ Z :=
  Adjunction.leftAdjointUniq (extendScalarsInverseImageAdjunction φ f)
    (inverseImageExtendScalarsAdjunction φ f)

/-- The comparison intertwines the two constructed composite units. -/
@[reassoc (attr := simp)] theorem inverseImageExtendScalarsIso_unit
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (extendScalarsInverseImageAdjunction φ f).unit.app F ≫
        (sheafRestrictScalars φ Z ⋙ directImage f (ModuleCat.{u} R)).map
          ((inverseImageExtendScalarsIso φ f).hom.app F) =
      (inverseImageExtendScalarsAdjunction φ f).unit.app F :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ F

/-- The comparison also intertwines the actual composite counits. -/
@[reassoc (attr := simp)] theorem inverseImageExtendScalarsIso_counit
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u} S)) :
    (inverseImageExtendScalarsIso φ f).hom.app
        ((sheafRestrictScalars φ Z ⋙ directImage f (ModuleCat.{u} R)).obj F) ≫
      (inverseImageExtendScalarsAdjunction φ f).counit.app F =
        (extendScalarsInverseImageAdjunction φ f).counit.app F :=
  Adjunction.leftAdjointUniq_hom_app_counit _ _ F

/-- The canonical map from a pulled-back R-sheaf to the restricted
pulled-back scalar extension. -/
def inverseImageScalarUnit (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (inverseImage f R).obj F ⟶
      (sheafRestrictScalars φ Z).obj
        ((inverseImage f S).obj ((sheafExtendScalars φ X).obj F)) :=
  (sheafExtensionUnit φ Z).app ((inverseImage f R).obj F) ≫
    (sheafRestrictScalars φ Z).map ((inverseImageExtendScalarsIso φ f).inv.app F)

/-- The actual scalar-extension universal correspondence on the pulled-back
source sheaf identifies the canonical scalar map with the inverse comparison. -/
theorem inverseImageScalarUnit_homEquiv
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (sheafExtendRestrictScalarsAdj φ Z).homEquiv _ _
      ((inverseImageExtendScalarsIso φ f).inv.app F) =
        inverseImageScalarUnit φ f F :=
  (sheafExtendRestrictScalarsAdj φ Z).homEquiv_unit _ _ _

/-- Scalar maps after geometric inverse image are natural in the coefficient sheaf. -/
def inverseImageScalarUnitNat :
    inverseImage f R ⟶
      sheafExtendScalars φ X ⋙ inverseImage f S ⋙ sheafRestrictScalars φ Z where
  app := inverseImageScalarUnit φ f
  naturality {F G} a := by
    dsimp only [inverseImageScalarUnit, Functor.comp_map]
    have hη := (sheafExtensionUnit φ Z).naturality ((inverseImage f R).map a)
    dsimp only [Functor.id_map, Functor.comp_map] at hη
    rw [← Category.assoc, hη]
    simp only [Category.assoc, ← Functor.map_comp]
    congr 1
    exact congrArg (fun b => (sheafRestrictScalars φ Z).map b)
      ((inverseImageExtendScalarsIso φ f).inv.naturality a)

end Langlands.Geometry.EtaleInverseImage
