import Langlands.Shimura.Coefficients.EtaleInverseImageAssociatedIso
import Langlands.Geometry.EtaleInverseImageConstant
import Langlands.Geometry.EtaleGeometricCoefficientDiagram

/-! # Constant product coordinates for geometric inverse image -/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Geometry Langlands.Geometry.EtaleInverseImage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z W : Scheme.{u}} (f : Z ⟶ X) (R : Type u) [CommRing R]

/-- Product base change followed by the canonical identification of constant coefficients. -/
def inverseImageConstantProductMap (V : X.Etale) (M : ModuleCat.{u} R) :
    (inverseImage f R).obj
        ((productSheaf X.smallEtaleTopology V).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M)) ⟶
      (productSheaf Z.smallEtaleTopology ((etaleObjectPullback f).obj V)).obj
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u} R)).obj M) :=
  inverseImageProductSheafMap f R V
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M) ≫
    (productSheaf Z.smallEtaleTopology ((etaleObjectPullback f).obj V)).map
      ((inverseImageConstantIso f R).hom.app M)

/-- Constant product coordinates commute with actual pullback of any cover morphism. -/
@[reassoc] theorem inverseImageConstantProductMap_coverPullback
    {V V' : X.Etale} (a : V' ⟶ V) (M : ModuleCat.{u} R) :
    (inverseImage f R).map
        (coverPullback X.smallEtaleTopology a
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M)) ≫
      inverseImageConstantProductMap f R V' M =
    inverseImageConstantProductMap f R V M ≫
      coverPullback Z.smallEtaleTopology ((etaleObjectPullback f).map a)
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u} R)).obj M) := by
  dsimp only [inverseImageConstantProductMap]
  rw [inverseImageProductSheafMap_coverPullback_assoc, coverPullback_natural]
  simp only [Category.assoc]

/-- The constant product comparisons compose through the actual inverse-image and
single-to-iterated cover comparisons. -/
@[reassoc] theorem inverseImageConstantProductMap_comp
    (g : W ⟶ Z) (V : X.Etale) (M : ModuleCat.{u} R) :
    (inverseImageComp R f g).hom.app
        ((productSheaf X.smallEtaleTopology V).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M)) ≫
      inverseImageConstantProductMap (g ≫ f) R V M =
    (inverseImage g R).map (inverseImageConstantProductMap f R V M) ≫
      inverseImageConstantProductMap g R ((etaleObjectPullback f).obj V) M ≫
        coverPullback W.smallEtaleTopology ((etaleObjectPullbackComp f g).hom.app V)
          ((constantSheaf W.smallEtaleTopology (ModuleCat.{u} R)).obj M) := by
  dsimp only [inverseImageConstantProductMap]
  rw [reassoc_of% (inverseImageProductSheafMap_comp f g R V
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M))]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [inverseImageProductSheafMap_natural_assoc]
  rw [← Functor.map_comp_assoc, ← inverseImageConstantIso_comp]
  rw [Functor.map_comp, Category.assoc, coverPullback_natural_assoc,
    coverPullback_natural]

/-- Equality transport of the base morphism retains the actual cover equality comparison. -/
@[reassoc] theorem inverseImageConstantProductMap_congr
    {k : Z ⟶ X} (e : f = k) (V : X.Etale) (M : ModuleCat.{u} R) :
    (inverseImageCongr R e).hom.app
        ((productSheaf X.smallEtaleTopology V).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M)) ≫
      inverseImageConstantProductMap k R V M ≫
        coverPullback Z.smallEtaleTopology ((etaleObjectPullbackCongr e).hom.app V)
          ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u} R)).obj M) =
    inverseImageConstantProductMap f R V M := by
  subst k
  have he : (etaleObjectPullbackCongr (rfl : f = f)).hom.app V = 𝟙 _ := by
    apply MorphismProperty.Over.Hom.ext
    change _ = 𝟙 (pullback V.hom f)
    apply pullback.hom_ext <;> simp
  rw [he, coverPullback_id, Category.comp_id, inverseImageCongr_refl]
  exact Category.id_comp _

end Langlands.Shimura.Coefficients
