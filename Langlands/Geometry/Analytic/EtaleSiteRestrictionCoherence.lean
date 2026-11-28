import Langlands.Geometry.Analytic.EtaleSiteBaseChange
import Mathlib.CategoryTheory.Sites.Whiskering

/-! # Coherence of restriction on small analytic étale sites -/

noncomputable section

universe u v a b a' b'

namespace Langlands.Analytic.SaturatedAtlasPresentation.EtaleSite

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y Z : LocalizedCategory.{u, v, v} (K := K)}
  {f : X ⟶ Y} {g : Y ⟶ Z} {fg : X ⟶ Z}
  (A : Type a) [Category.{b} A]

/-- Restriction of a sheaf by precomposition with the étale test postcomposition functor. -/
abbrev restriction (hf : etale f) : Sheaf (etaleTopology Y) A ⥤ Sheaf (etaleTopology X) A :=
  (postcomposeEtale hf).sheafPushforwardContinuous A (etaleTopology X) (etaleTopology Y)

local instance : (etale (K := K) :
    MorphismProperty (LocalizedCategory.{u, v, v} (K := K))).IsMultiplicative where
  id_mem X := etale_of_isIso (𝟙 X)
  comp_mem _ _ := etale_comp

/-- Restriction along an étale arrow equal to the identity identifies with the identity functor. -/
def restrictionId {i : X ⟶ X} (hi : etale i) (e : i = 𝟙 X) :
    restriction A hi ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.mapId (P := etale) ⊤ X i e) A (etaleTopology X)

/-- Successive restrictions identify with restriction along an étale arrow equal to the
composite. -/
def restrictionComp (hf : etale f) (hg : etale g) (hfg : etale fg) (e : fg = f ≫ g) :
    restriction A hg ⋙ restriction A hf ≅ restriction A hfg :=
  Functor.sheafPushforwardContinuousComp'
    (MorphismProperty.Over.mapComp ⊤ hf hg fg e).symm
    A (etaleTopology X) (etaleTopology Y) (etaleTopology Z)

variable {A} {B : Type a'} [Category.{b'} B] (F : A ⥤ B)
  [(etaleTopology X).HasSheafCompose F]

/-- Precomposition by the site functor commutes with postcomposition by a functor
preserving the sheaf condition. -/
def restrictionSheafComposeIso (hf : etale f) [(etaleTopology Y).HasSheafCompose F] :
    sheafCompose (etaleTopology Y) F ⋙ restriction B hf ≅
      restriction A hf ⋙ sheafCompose (etaleTopology X) F :=
  Iso.refl _

/-- Change of coefficients commutes with the identity comparison for restriction. -/
theorem restrictionSheafComposeIso_id {i : X ⟶ X} (hi : etale i) (e : i = 𝟙 X)
    (P : Sheaf (etaleTopology X) A) :
    (restrictionSheafComposeIso F hi).hom.app P ≫
        (sheafCompose (etaleTopology X) F).map ((restrictionId A hi e).hom.app P) =
      (restrictionId B hi e).hom.app ((sheafCompose (etaleTopology X) F).obj P) := by
  change 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change F.map (P.obj.map _ ≫ 𝟙 _) = F.map (P.obj.map _) ≫ 𝟙 _
  rw [Category.comp_id, Category.comp_id]

/-- Change of coefficients commutes with the composition comparison for restriction. -/
theorem restrictionSheafComposeIso_comp
    [(etaleTopology Y).HasSheafCompose F] [(etaleTopology Z).HasSheafCompose F]
    (hf : etale f) (hg : etale g) (hfg : etale fg) (e : fg = f ≫ g)
    (P : Sheaf (etaleTopology Z) A) :
    (restriction B hf).map ((restrictionSheafComposeIso F hg).hom.app P) ≫
        (restrictionSheafComposeIso F hf).hom.app ((restriction A hg).obj P) ≫
        (sheafCompose (etaleTopology X) F).map ((restrictionComp A hf hg hfg e).hom.app P) =
      (restrictionComp B hf hg hfg e).hom.app ((sheafCompose (etaleTopology Z) F).obj P) ≫
        (restrictionSheafComposeIso F hfg).hom.app P := by
  change (restriction B hf).map (𝟙 _) ≫ 𝟙 _ ≫ _ = _ ≫ 𝟙 _
  rw [(restriction B hf).map_id, Category.id_comp, Category.id_comp, Category.comp_id]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change F.map (𝟙 _ ≫ P.obj.map _) = 𝟙 _ ≫ F.map (P.obj.map _)
  rw [Category.id_comp, Category.id_comp]

end Langlands.Analytic.SaturatedAtlasPresentation.EtaleSite
