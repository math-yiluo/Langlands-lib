/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RestrictedDerivedEvaluationPullback
import WeilConjectures.AlgebraicGeometry.EtaleObjectSections

/-! # Pullback of the represented identity section

Source: Stacks Project, Tag 03Q8 and Cohomology on Sites, Tag 0BKV.
(blueprint: lem-sbc-restricted-comparison-generator-pullback).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.RawRestrictedComparison

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem sectionsIso_inv_eq {Y : Scheme.{v}} (W : Y.Etale)
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    (sectionsIso W G).inv = (etaleObjectSectionsIso W).hom.app G := by
  unfold sectionsIso etaleObjectSectionsIso
  dsimp
  simp only [Category.assoc]
  congr 1
  exact ((Sheaf.ΓNatIsoSheafSections W.left.smallEtaleTopology AddCommGrpCat.{v + 1}
    (MorphismProperty.Over.mkIdTerminal @Etale W.left)).inv.naturality
      ((upperStarIsoLocalizationRestriction AddCommGrpCat.{v + 1} W.hom W.prop).inv.app G)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Naturality of ordinary section restriction, obtained from the existing etale-object
section square and naturality in the coefficient map. -/
private theorem restrictedSections_pullback_square {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (G' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (ψ : (upperStar AddCommGrpCat.{v + 1} a).obj G ⟶ G') (U : S.Etale) :
    (sectionsIso ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U) G).inv ≫
      globalSectionsUpperStarMap AddCommGrpCat.{v + 1} (rawAffineRestrictedMap a h h' w U)
        ((upperStar AddCommGrpCat.{v + 1} (Limits.pullback.snd U.hom h)).obj G) ≫
      (Sheaf.Γ (Limits.pullback U.hom h').smallEtaleTopology AddCommGrpCat.{v + 1}).map
        (rawAffineRestrictedCoefficient a h h' w G G' ψ U) ≫
      (sectionsIso ((MorphismProperty.Over.pullback @Etale ⊤ h').obj U) G').hom =
    ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} a).unit.app G).hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)) ≫
      ((lowerStarComp AddCommGrpCat.{v + 1} a h h' w.symm).hom.app
        ((upperStar AddCommGrpCat.{v + 1} a).obj G)).hom.app (op U) ≫
      ψ.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ h').obj U)) := by
  let W : Y.Etale := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
  let W' : Y'.Etale := (MorphismProperty.Over.pullback @Etale ⊤ h').obj U
  let q := rawAffineRestrictedMap a h h' w U
  let Γ' := Sheaf.Γ W'.left.smallEtaleTopology AddCommGrpCat.{v + 1}
  let k := (upperStarComp AddCommGrpCat.{v + 1} q W.hom).inv.app G ≫
    (upperStarComp AddCommGrpCat.{v + 1} W'.hom a (q ≫ W.hom)
      (by simp [q, W, W', rawAffineRestrictedMap])).hom.app G
  have hb := etaleObjectSections_baseChange U a h h' w.symm q
    (by simp [q, rawAffineRestrictedMap])
    (by simp [q, rawAffineRestrictedMap]) G
  have hn := (etaleObjectSectionsIso W').hom.naturality ψ
  rw [sectionsIso_inv_eq]
  have hc : rawAffineRestrictedCoefficient a h h' w G G' ψ U =
      k ≫ (upperStar AddCommGrpCat.{v + 1} W'.hom).map ψ := by rfl
  change (((lowerStar AddCommGrpCat.{v + 1} h).map
    ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} a).unit.app G) ≫
      (lowerStarComp AddCommGrpCat.{v + 1} a h h' w.symm).hom.app _).hom.app (op U)) ≫
      (etaleObjectSectionsIso W').hom.app ((upperStar AddCommGrpCat.{v + 1} a).obj G) =
    (etaleObjectSectionsIso W).hom.app G ≫
      globalSectionsUpperStarMap AddCommGrpCat.{v + 1} q _ ≫ Γ'.map k at hb
  rw [hc, Functor.map_comp]
  simp only [Category.assoc]
  erw [← reassoc_of% hb, ← reassoc_of% hn]
  rw [← sectionsIso_inv_eq]
  erw [Iso.inv_hom_id]
  simp only [Category.comp_id]
  rfl


set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Pullback transports the represented identity generator in zeroth derived sections.
This has no degree p, target coefficient sheaf, or raw derived-Hom class.
Source: Stacks Project, Tag 03Q8; Cohomology on Sites, Tag 0BKV.
(blueprint: lem-sbc-restricted-comparison-generator-pullback).

Proof: Write A = the sheafification of the free abelian presheaf represented by U,
G = h^* A and G' = h'^* A. Cancel the zeroIso at the source of transportZero
against its inverse. The remaining input is generator h U, namely the identity
section of A at U, mapped by the unit for h, then by sectionsIso inverse.
Write q = U times_S a, r = pr_Y and r' = pr_Y'. The pullback projection equations
give r' followed by a equals q followed by r. Expanding the restricted coefficient
map with the inverse-image composition comparisons identifies the two restrictions
of A along these equal morphisms. Naturality of the inverse-image adjunction unit,
and its composition formula, show that pulling the unit for h across q and applying
the comparison for a followed by h gives exactly the unit for h'. The terminal
object comparisons in globalSectionsUpperStarMap and sectionsIso agree: both send
the identity etale object of V' to the base change of U. Thus the resulting section
is generator h' U. Postcompose with zeroIso inverse for G' to obtain the stated
identity. This uses no higher derived morphism and no invertibility of the section
pullback. Identity maps, degree-zero sections, and empty schemes obey the same unit
and terminal-object equations. -/
theorem restrictedComparison_generator_pullback {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (U : S.Etale) :
    transportZero a h h' w
      ((upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U))
      ((upperStar AddCommGrpCat.{v + 1} h').obj (freeSheaf S U))
      ((upperStarComp AddCommGrpCat.{v + 1} a h h' w.symm).inv.app (freeSheaf S U)) U
      ((zeroIso ((MorphismProperty.Over.pullback @Etale ⊤ h).obj U)
        ((upperStar AddCommGrpCat.{v + 1} h).obj (freeSheaf S U))).inv (generator h U)) =
    (zeroIso ((MorphismProperty.Over.pullback @Etale ⊤ h').obj U)
      ((upperStar AddCommGrpCat.{v + 1} h').obj (freeSheaf S U))).inv (generator h' U) := by
  let A := freeSheaf S U
  let G := (upperStar AddCommGrpCat.{v + 1} h).obj A
  let G' := (upperStar AddCommGrpCat.{v + 1} h').obj A
  let e := upperStarComp AddCommGrpCat.{v + 1} a h h' w.symm
  let W : Y.Etale := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
  let W' : Y'.Etale := (MorphismProperty.Over.pullback @Etale ⊤ h').obj U
  let b := globalSectionsUpperStarMap AddCommGrpCat.{v + 1}
      (rawAffineRestrictedMap a h h' w U)
      ((upperStar AddCommGrpCat.{v + 1} W.hom).obj G) ≫
    (Sheaf.Γ W'.left.smallEtaleTopology AddCommGrpCat.{v + 1}).map
      (rawAffineRestrictedCoefficient a h h' w G G' (e.inv.app A) U)
  have hsections := restrictedSections_pullback_square a h h' w G G' (e.inv.app A) U
  have hunit := upperStarComp_hom_app_unit_app AddCommGrpCat.{v + 1} a h A h' w.symm
  rw [Adjunction.comp_unit_app] at hunit
  have hu :
      (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} h).unit.app A ≫
        (lowerStar AddCommGrpCat.{v + 1} h).map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} a).unit.app G) ≫
        (lowerStarComp AddCommGrpCat.{v + 1} a h h' w.symm).hom.app
          ((upperStar AddCommGrpCat.{v + 1} a).obj G) ≫
        (lowerStar AddCommGrpCat.{v + 1} h').map (e.inv.app A) =
      (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} h').unit.app A := by
    rw [← Category.assoc, ← Category.assoc, ← hunit]
    dsimp only [e]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have heval := congrArg (fun f ↦ f.hom.app (op U)) hu
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app] at heval
  have hgen : b (generator h U) = generator h' U := by
    apply (ConcreteCategory.bijective_of_isIso (sectionsIso W' G').hom).1
    let x : A.obj.obj (op U) :=
      (toSheafify S.smallEtaleTopology
        (uliftYoneda.{v + 1}.obj U ⋙ AddCommGrpCat.free)).app (op U)
          (FreeAbelianGroup.of (ULift.up (𝟙 U)))
    change (((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} h).unit.app A).hom.app
      (op U) ≫ (sectionsIso W G).inv ≫ b ≫ (sectionsIso W' G').hom) x =
        (sectionsIso W' G').hom ((sectionsIso W' G').inv
          (((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} h').unit.app A).hom.app
            (op U) x))
    erw [Iso.inv_hom_id_apply]
    change (sectionsIso W G).inv ≫ b ≫ (sectionsIso W' G').hom = _ at hsections
    erw [hsections, heval]
    rfl
  unfold transportZero
  simp only [AddCommGrpCat.comp_apply]
  erw [Iso.inv_hom_id_apply]
  exact congrArg (zeroIso W' G').inv hgen

end AlgebraicGeometry.Etale.RawRestrictedComparison
