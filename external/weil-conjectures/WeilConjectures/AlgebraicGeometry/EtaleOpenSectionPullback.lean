/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.ConstantSectionAdjunctPullback
import WeilConjectures.AlgebraicGeometry.NestedOpenSectionUnit

/-! # Restriction of sections classified by a constant sheaf map

Source: Stacks Project, Tag 03F3, localization restriction and adjunction units.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Classifying a section after pullback between nested opens gives its restriction.
Source: Stacks Project, Tag 03F3, localization restriction; the unit compatibility
calculation of `open_restriction_pullback_unit`.
(blueprint: lem-weil-pbc-etale-open-section-pullback)

Proof: Expand the constant pullback comparison as the unique left adjoint comparison.
Under the constant-sheaf adjunction the pulled-back map is the original section
followed by the inverse-image unit and the terminal-object pullback identification.
Apply the open restriction unit calculation to U.ι and V. The fibre product of V
and U over X identifies with V, since V is contained in U. The composition unit law
then cancels the inverse composition comparison in the displayed map. The remaining
section map is F evaluated on the inclusion from V to U, conjugated by the two
localization restriction comparisons. Naturality of these comparisons gives precisely
the displayed expression. The argument uses only terminal-object uniqueness and
monomorphy of open immersions, so also applies to empty or equal opens. -/
theorem etaleOpenSection_pullback {X : Scheme.{u}}
    (U V : X.Opens) (h : V ≤ U)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (m : (constantSheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶
      (Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj F) :
    let bU := Scheme.Etale.mk (𝟙 U.toScheme)
    let bV := Scheme.Etale.mk (𝟙 V.toScheme)
    let vU := (MorphismProperty.Over.map ⊤ (inferInstance : Etale U.ι)).obj bU
    let vV := (MorphismProperty.Over.map ⊤ (inferInstance : Etale V.ι)).obj bV
    let f : vV ⟶ vU := MorphismProperty.Over.homMk (X.homOfLE h)
      (by
        change X.homOfLE h ≫ (𝟙 U.toScheme ≫ U.ι) = 𝟙 V.toScheme ≫ V.ι
        simpa only [Category.id_comp] using X.homOfLE_ι h) trivial
    AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((constantSheafAdj V.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}
        (show IsTerminal bV from IsTerminal.ofUniqueHom
          (fun a ↦ MorphismProperty.Over.homMk a.hom (Category.comp_id _))
          (fun a f ↦ by
            apply MorphismProperty.Over.Hom.ext
            exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w f)))).homEquiv _ _
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          (X.homOfLE h)).inv.app (AddCommGrpCat.of (ULift ℤ)) ≫
          (Etale.upperStar AddCommGrpCat.{u + 1} (X.homOfLE h)).map m ≫
          (Etale.upperStarComp AddCommGrpCat.{u + 1} (X.homOfLE h) U.ι V.ι
            (X.homOfLE_ι h).symm).inv.app F)) =
      (((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} V.ι
        inferInstance).inv.app F).hom.app (op bV))
        (F.obj.map f.op
          ((((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} U.ι
            inferInstance).hom.app F).hom.app (op bU))
            (AddCommGrpCat.uliftZMultiplesAddEquiv _
              ((constantSheafAdj U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}
                (show IsTerminal bU from IsTerminal.ofUniqueHom
                  (fun a ↦ MorphismProperty.Over.homMk a.hom (Category.comp_id _))
                  (fun a f ↦ by
                    apply MorphismProperty.Over.Hom.ext
                    exact (Category.comp_id _).symm.trans
                      (MorphismProperty.Over.w f)))).homEquiv _ _ m)))) := by
  dsimp only
  simp only [← Category.assoc]
  rw [Adjunction.homEquiv_naturality_right]
  rw [constantSection_adjunct_pullback]
  have hz {B C : AddCommGrpCat.{u + 1}}
      (f : AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ B) (g : B ⟶ C) :
      AddCommGrpCat.uliftZMultiplesAddEquiv C (f ≫ g) =
        g (AddCommGrpCat.uliftZMultiplesAddEquiv B f) := by rfl
  rw [hz, hz]
  have hn := nestedOpenSection_unit U V h F
  dsimp only at hn
  let e := Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} V.ι
    (inferInstance : Etale V.ι)
  have hinv : (e.hom.app F).hom.app (op (Scheme.Etale.mk (𝟙 V.toScheme))) ≫
      (e.inv.app F).hom.app (op (Scheme.Etale.mk (𝟙 V.toScheme))) = 𝟙 _ := by
    exact (((sheafSections V.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (Scheme.Etale.mk (𝟙 V.toScheme)))).mapIso (e.app F)).hom_inv_id
  have hn' := congrArg
    (fun q ↦ q ≫ (e.inv.app F).hom.app (op (Scheme.Etale.mk (𝟙 V.toScheme)))) hn
  dsimp only [e] at hinv hn'
  simp only [Category.assoc, hinv, Category.comp_id] at hn'
  exact ConcreteCategory.congr_hom hn' _

end AlgebraicGeometry
