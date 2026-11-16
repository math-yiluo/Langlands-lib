import Langlands.GroupScheme.Dynamic.MonomorphismCellPreimage
import Langlands.GroupScheme.Dynamic.BaseUnipotentMonomorphism
import Langlands.GroupScheme.ImageGenerationSubgroup
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Closedness over the dynamic triple cell -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {H G MH ZH UH MG ZG UG : GroupScheme S}
    (χ : (Gm S).toGrp ⟶ H) (f : H ⟶ G)
    {iM : MH ⟶ H} {iZ : ZH ⟶ H} {iU : UH ⟶ H}
    {jM : MG ⟶ G} {jZ : ZG ⟶ G} {jU : UG ⟶ G}
    (hM : (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom S (-1)) ≫ χ)).IsRepresentedBy iM)
    (hZ : (centralizer χ).IsRepresentedBy iZ)
    (hU : (unipotent χ).IsRepresentedBy iU)
    (hMG : (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom S (-1)) ≫ (χ ≫ f))).IsRepresentedBy jM)
    (hZG : (centralizer (χ ≫ f)).IsRepresentedBy jZ)
    (hUG : (unipotent (χ ≫ f)).IsRepresentedBy jU)

/-- The induced map on the actual triple cells is closed as soon as its
centralizer factor is closed. The unipotent factors need only ambient monicity. -/
theorem isClosedImmersion_tripleCellFactor
    [IsAffineHom H.X.hom] [IsAffineHom G.X.hom] [Mono f.hom.hom]
    (hz : IsClosedSubgroup
      (hZ.restrictionHom hZG f (centralizer_le_comap χ f))) :
    IsClosedImmersion (tripleCellFactor χ f hM hZ hU hMG hZG hUG).left := by
  let m := hM.restrictionHom hMG f (by
    simpa only [Category.assoc] using
      unipotent_le_comap (CommGroupScheme.groupHom (Gm.powerHom S (-1)) ≫ χ) f)
  let z := hZ.restrictionHom hZG f (centralizer_le_comap χ f)
  let v := hU.restrictionHom hUG f (unipotent_le_comap χ f)
  have : IsClosedImmersion m.hom.hom.left :=
    isClosedSubgroup_unipotent_of_represented_overBase
      (CommGroupScheme.groupHom (Gm.powerHom S (-1)) ≫ χ) f hM
      (by simpa only [Category.assoc] using hMG) m
      (hM.restrictionHom_comp hMG f _)
  have : IsClosedImmersion z.hom.hom.left := hz
  have : IsClosedImmersion v.hom.hom.left :=
    isClosedSubgroup_unipotent_of_represented_overBase χ f hU hUG v
      (hU.restrictionHom_comp hUG f _)
  have : IsClosedImmersion (z.hom.hom ⊗ₘ v.hom.hom).left :=
    ImageGeneration.isClosedImmersion_tensorHom_left _ _
  exact ImageGeneration.isClosedImmersion_tensorHom_left m.hom.hom
    (z.hom.hom ⊗ₘ v.hom.hom)

include χ hM hZ hU hMG hZG hUG in
/-- On the source triple cell, the ambient map is a locally closed immersion
when the centralizer factor is closed. -/
theorem isImmersion_tripleCellMultiplication_comp
    [IsAffineHom H.X.hom] [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [Mono f.hom.hom]
    (hz : IsClosedSubgroup
      (hZ.restrictionHom hZG f (centralizer_le_comap χ f))) :
    IsImmersion ((tripleCellMultiplication iM iZ iU).left ≫ f.hom.hom.left) := by
  have : IsClosedImmersion (tripleCellFactor χ f hM hZ hU hMG hZG hUG).left :=
    isClosedImmersion_tripleCellFactor χ f hM hZ hU hMG hZG hUG hz
  have : IsOpenImmersion (tripleCellMultiplication jM jZ jU).left :=
    isOpenImmersion_tripleCellMultiplication_overBase (χ ≫ f) hMG hZG hUG
  rw [← Over.comp_left, ← tripleCellFactor_comp χ f hM hZ hU hMG hZG hUG,
    Over.comp_left]
  infer_instance

variable [Smooth H.X.hom] [IsAffineHom H.X.hom] [GeometricallyConnected H.X.hom]
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [Mono f.hom.hom]

/-- The source triple cell, with its actual multiplication map, is canonically
the inverse image of the target triple cell. -/
def tripleCellPullbackIso :
    (MH.X ⊗ (ZH.X ⊗ UH.X)).left ≅
      pullback f.hom.hom.left (tripleCellMultiplication jM jZ jU).left :=
  (isPullback_tripleCellFactor χ f hM hZ hU hMG hZG hUG).flip.isoPullback

theorem tripleCellPullbackIso_hom_fst :
    (tripleCellPullbackIso χ f hM hZ hU hMG hZG hUG).hom ≫
        pullback.fst f.hom.hom.left (tripleCellMultiplication jM jZ jU).left =
      (tripleCellMultiplication iM iZ iU).left :=
  (isPullback_tripleCellFactor χ f hM hZ hU hMG hZG hUG).flip.isoPullback_hom_fst

theorem tripleCellPullbackIso_hom_snd :
    (tripleCellPullbackIso χ f hM hZ hU hMG hZG hUG).hom ≫
        pullback.snd f.hom.hom.left (tripleCellMultiplication jM jZ jU).left =
      (tripleCellFactor χ f hM hZ hU hMG hZG hUG).left :=
  (isPullback_tripleCellFactor χ f hM hZ hU hMG hZG hUG).flip.isoPullback_hom_snd

include χ hM hZ hU hMG hZG hUG in
/-- The ambient map pulled back to the target triple cell is a closed
immersion when the centralizer factor is closed. -/
theorem isClosedImmersion_pullback_tripleCellMultiplication
    (hz : IsClosedSubgroup
      (hZ.restrictionHom hZG f (centralizer_le_comap χ f))) :
    IsClosedImmersion
      (pullback.snd f.hom.hom.left (tripleCellMultiplication jM jZ jU).left) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (tripleCellPullbackIso χ f hM hZ hU hMG hZG hUG).hom,
    tripleCellPullbackIso_hom_snd]
  exact isClosedImmersion_tripleCellFactor χ f hM hZ hU hMG hZG hUG hz

end Langlands.GroupScheme.Dynamic
