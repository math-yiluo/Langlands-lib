/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.EtaleRestrictionPullbackUnit

/-!
# Open restriction and pullback units

Source: Stacks Project, Cohomology on Sites, Tag 03F3, localization and restriction;
agent-identified compatibility gap in the étale Mayer–Vietoris argument.
(blueprint: lem-weil-pbc-open-restriction-pullback-unit)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Pulling back a section along the restriction of a morphism to an open is pulling
back along the original morphism, under the canonical restriction comparisons.
Source: Stacks Project, Cohomology on Sites, Tag 03F3, localization and restriction;
agent-identified gap, with the following proof from adjunction unit equations.
(blueprint: lem-weil-pbc-open-restriction-pullback-unit)

1. Identify the seven fibre products P₀,...,P₆ of the node's proof with W or W'.
   The projections are isomorphisms by the universal property and the monomorphism
   property of open immersions. All comparison maps over Y agree by uniqueness.
   Use def-pc-fibre-product, lem-weil-pbc-open-immersion-monomorphism,
   lem-weil-pbc-open-fibre-product, def-weil-pbc-direct-image and
   lem-weil-pbc-inverse-image-composition (1).
2. By lem-weil-pbc-etale-inverse-image-restriction (2) and naturality, the units
   of the two open immersions on these sections are the inverses of rhoF and rhoG.
3. Evaluate lem-weil-pbc-inverse-image-composition (2) for (jW,gW) at W.
   By def-weil-pbc-direct-image and naturality of the unit from
   def-weil-pbc-inverse-image, obtain c(jW,gW) eta(gW) rhoF⁻¹ = eta(h).
4. Evaluate the same unit equation for (g,jW') at W. Naturality and the same
   identifications give c(g,jW') rhoG⁻¹ eta(g) = eta(h).
5. Equate these formulas, cancel c(g,jW'), and compose with rhoG and rhoF.
   The result is the equality below, hence the required equality on every section.

The statement is written without `let`. The site morphism (g_W, id) from W' into the
fibre product W ×_W W' and the morphism (g_W, j_W') from W' into W ×_X Y (the inverse of
the canonical open-fibre-product identification) carry the sections of the direct images
to W'. The identity-scheme morphisms remove identity composites in the terminal objects
of the restriction comparisons. The equality of group homomorphisms is precisely the
node's pointwise equality for every a, without a choice of sections.
-/
theorem open_restriction_pullback_unit {X Y : Scheme.{u}} (g : Y ⟶ X) (W : X.Opens)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (morphismRestrict g W)).unit.app
        ((Etale.upperStar AddCommGrpCat.{u + 1} W.ι).obj F)).hom.app
          (op (Scheme.Etale.mk (𝟙 W.toScheme))) ≫
      ((Etale.upperStar AddCommGrpCat.{u + 1} (morphismRestrict g W)).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} W.ι).obj F)).obj.map
        (MorphismProperty.Over.homMk
          (pullback.lift (morphismRestrict g W) (𝟙 (g ⁻¹ᵁ W).toScheme)
            ((Category.comp_id _).trans (Category.id_comp _).symm))
          (by simp) :
          Scheme.Etale.mk (𝟙 (g ⁻¹ᵁ W).toScheme) ⟶
            (MorphismProperty.Over.pullback @Etale ⊤ (morphismRestrict g W)).obj
              (Scheme.Etale.mk (𝟙 W.toScheme))).op ≫
      ((Etale.upperStarComp AddCommGrpCat.{u + 1} (morphismRestrict g W) W.ι).inv.app F ≫
          (Etale.upperStarComp AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι g
            (morphismRestrict g W ≫ W.ι) (morphismRestrict_ι g W)).hom.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 (g ⁻¹ᵁ W).toScheme))) ≫
      ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι
          inferInstance).hom.app ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj F)).hom.app
        (op (Scheme.Etale.mk (𝟙 (g ⁻¹ᵁ W).toScheme))) ≫
      ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj F).obj.map
        (MorphismProperty.Over.homMk (𝟙 (g ⁻¹ᵁ W).toScheme)
          ((Category.id_comp _).trans (Category.id_comp _)) :
          Scheme.Etale.mk (g ⁻¹ᵁ W).ι ⟶
            (MorphismProperty.Over.map ⊤ (inferInstance : Etale (g ⁻¹ᵁ W).ι)).obj
              (Scheme.Etale.mk (𝟙 (g ⁻¹ᵁ W).toScheme))).op =
    ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} W.ι
          inferInstance).hom.app F).hom.app (op (Scheme.Etale.mk (𝟙 W.toScheme))) ≫
      F.obj.map
        (MorphismProperty.Over.homMk (𝟙 W.toScheme)
          ((Category.id_comp _).trans (Category.id_comp _)) :
          Scheme.Etale.mk W.ι ⟶
            (MorphismProperty.Over.map ⊤ (inferInstance : Etale W.ι)).obj
              (Scheme.Etale.mk (𝟙 W.toScheme))).op ≫
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app F).hom.app
        (op (Scheme.Etale.mk W.ι)) ≫
      ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj F).obj.map
        (MorphismProperty.Over.homMk
          (pullback.lift (morphismRestrict g W) (g ⁻¹ᵁ W).ι (morphismRestrict_ι g W))
          (by simp) :
          Scheme.Etale.mk (g ⁻¹ᵁ W).ι ⟶
            (MorphismProperty.Over.pullback @Etale ⊤ g).obj (Scheme.Etale.mk W.ι)).op := by
  let p : W.toScheme ⟶ X := W.ι
  let p' : (g ⁻¹ᵁ W).toScheme ⟶ Y := (g ⁻¹ᵁ W).ι
  let g' := morphismRestrict g W
  let ι := pullback.lift g' p' (morphismRestrict_ι g W)
  have hι : IsIso ι := by
    have he : (isPullback_morphismRestrict g W).isoPullback.hom = ι := by
      apply pullback.hom_ext <;> simp [ι, g', p']
    rw [← he]
    infer_instance
  let _ : IsIso ι := hι
  have hι₁ : ι ≫ pullback.fst p g = g' := by simp [ι, p, g']
  have hι₂ : ι ≫ pullback.snd p g = p' := by simp [ι, p, p']
  have h := etale_restriction_pullback_unit g p g' p' (by simp [p, p', g']) ι hι₁ hι₂
  obtain ⟨hp', h⟩ := h
  convert h F using 1 <;>
    simp [p, p', g', ι, MorphismProperty.Over.isoMk, MorphismProperty.Comma.isoMk,
    MorphismProperty.Comma.isoFromComma, CategoryTheory.Comma.isoMk,
    MorphismProperty.Comma.homFromCommaOfIsIso, MorphismProperty.Over.homMk,
    CategoryTheory.Over.homMk] <;> rfl

end AlgebraicGeometry
