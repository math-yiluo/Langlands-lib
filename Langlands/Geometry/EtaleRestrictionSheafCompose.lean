import Langlands.Geometry.EtalePullback
import Mathlib.CategoryTheory.Sites.Whiskering

/-! # Étale restriction and postcomposition of sheaves -/

noncomputable section

namespace Langlands.Geometry.EtalePullback

open CategoryTheory AlgebraicGeometry

universe u uA uB vA vB

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  (F : A ⥤ B) {X Y Z : Scheme.{u}}

/-- Postcomposition by a functor preserving the sheaf condition on both sites
commutes with restriction along an étale morphism. -/
def restrictionSheafComposeIso (f : Y ⟶ X) [Etale f]
    [X.smallEtaleTopology.HasSheafCompose F] [Y.smallEtaleTopology.HasSheafCompose F] :
    sheafCompose X.smallEtaleTopology F ⋙ restriction f B ≅
      restriction f A ⋙ sheafCompose Y.smallEtaleTopology F :=
  Iso.refl _

/-- The comparison for the identity arrow is compatible with identity restriction. -/
theorem restrictionSheafComposeIso_id [X.smallEtaleTopology.HasSheafCompose F]
    (P : Sheaf X.smallEtaleTopology A) :
    (restrictionSheafComposeIso F (𝟙 X)).hom.app P ≫
        (sheafCompose X.smallEtaleTopology F).map ((restrictionId A).hom.app P) =
      (restrictionId B).hom.app ((sheafCompose X.smallEtaleTopology F).obj P) := by
  change 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change F.map (P.obj.map _ ≫ 𝟙 _) = F.map (P.obj.map _) ≫ 𝟙 _
  rw [Category.comp_id, Category.comp_id]

/-- The comparisons for successive restrictions paste to the comparison for the
composite étale morphism via the canonical restriction composition maps. -/
theorem restrictionSheafComposeIso_comp (f : Y ⟶ X) [Etale f] (g : Z ⟶ Y) [Etale g]
    [X.smallEtaleTopology.HasSheafCompose F] [Y.smallEtaleTopology.HasSheafCompose F]
    [Z.smallEtaleTopology.HasSheafCompose F] (P : Sheaf X.smallEtaleTopology A) :
    (restriction g B).map ((restrictionSheafComposeIso F f).hom.app P) ≫
        (restrictionSheafComposeIso F g).hom.app ((restriction f A).obj P) ≫
        (sheafCompose Z.smallEtaleTopology F).map ((restrictionComp f A g).hom.app P) =
      (restrictionComp f B g).hom.app ((sheafCompose X.smallEtaleTopology F).obj P) ≫
        (restrictionSheafComposeIso F (g ≫ f)).hom.app P := by
  change (restriction g B).map (𝟙 _) ≫ 𝟙 _ ≫ _ = _ ≫ 𝟙 _
  rw [(restriction g B).map_id, Category.id_comp, Category.id_comp, Category.comp_id]
  rfl

end Langlands.Geometry.EtalePullback
