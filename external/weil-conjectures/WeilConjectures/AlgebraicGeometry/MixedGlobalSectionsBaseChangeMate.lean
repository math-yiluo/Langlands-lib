/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomPullbackComparison
public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
import WeilConjectures.AlgebraicGeometry.MixedSectionsBaseChangeUnitSquare

/-! # Leray comparison and the base-change mate
Source: Stacks Project, cohomology.tex, Remark 08HY; duality.tex, Tag 0AA8,
lemma-more-base-change, final comparison diagrams.
(blueprint: lem-sc-mixed-global-sections-base-change-mate).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

/-- Leray transfers the base-change mate of any map between sheaf complexes.
This statement has no internal Hom or tensor-Hom input.
Source: Stacks Project, cohomology.tex, Remark 08HY; duality.tex, Tag 0AA8,
lemma-more-base-change, final comparison diagrams.
(blueprint: lem-sc-mixed-global-sections-base-change-mate).

Proof: apply mixedSectionsBaseChange_unit_square to E and precompose with
inverse Leray for f. Cancel the adjacent inverse and forward Leray components.
To recover an arbitrary a, cancel postcomposition by restricted Leray for f' at E'.
Expand the adjunction transposes as the units followed by direct image. Naturality
of Leray for g moves the base-change component and direct image of a to restricted
global sections. Naturality of Leray for f' moves a past that comparison.
On the other path, naturality of Leray for g_X and of the scalar-square
isomorphism moves a to the same final twice-restricted global-sections map.
The unit-square equation now identifies the prefixes of these two paths.
Functoriality and associativity give the stated equality. -/
theorem mixedGlobalSections_baseChange_mate
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (E : schemeDerivedCategory X) (E' : schemeDerivedCategory (pullback f g))
    (a : (derivedPullback (pullback.fst f g)).obj E ⟶ E') :
    (schemeGlobalScalarRestriction f).map
        ((schemeDerivedGlobalSections X).map
          ((schemeHomPullbackAdjunction (pullback.fst f g)).homEquiv _ _ a) ≫
          (mixedGlobalSectionsDirectImageIso (pullback.fst f g)).hom.app E') ≫
      (schemeGlobalScalarSquareIso f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition).hom.app ((schemeDerivedGlobalSections (pullback f g)).obj E') ≫
      (schemeGlobalScalarRestriction g).map
        ((mixedGlobalSectionsDirectImageIso (pullback.snd f g)).inv.app E') =
    (mixedGlobalSectionsDirectImageIso f).inv.app E ≫
      (schemeDerivedGlobalSections Y).map
        ((schemeHomPullbackAdjunction g).homEquiv _ _
          (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
            pullback.condition E ≫
            (schemeDerivedDirectImage (pullback.snd f g)).map a)) ≫
      (mixedGlobalSectionsDirectImageIso g).hom.app
        ((schemeDerivedDirectImage (pullback.snd f g)).obj E') := by
  let b := mixedGlobalSectionsDirectImageIso f
  let e := mixedGlobalSectionsDirectImageIso (pullback.snd f g)
  let S := schemeGlobalScalarRestriction g
  have hu := mixedSectionsBaseChange_unit_square f g E
  have hu' := congrArg (fun k ↦ b.inv.app E ≫ k) hu
  change b.inv.app E ≫ _ = b.inv.app E ≫ b.hom.app E ≫ _ at hu'
  simp only [Functor.map_comp, Iso.inv_hom_id_app_assoc] at hu'
  apply (cancel_mono (S.map (e.hom.app E'))).mp
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  have hg := (mixedGlobalSectionsDirectImageIso g).hom.naturality
    (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
      pullback.condition E ≫ (schemeDerivedDirectImage (pullback.snd f g)).map a)
  dsimp only [Functor.comp_map] at hg
  simp only [Functor.map_comp] at hg
  simp only [Category.assoc] at hg ⊢
  rw [reassoc_of% hg]
  have hcancel : S.map (e.inv.app E') ≫ S.map (e.hom.app E') = 𝟙 _ := by
    rw [← S.map_comp, e.inv_hom_id_app, S.map_id]
  dsimp only [S, e] at hcancel
  rw [hcancel]
  have hn := e.hom.naturality a
  dsimp only [Functor.comp_map] at hn
  have hn' := congrArg (fun k ↦ S.map k) hn
  simp only [Functor.map_comp] at hn'
  rw [hn']
  have hs := (schemeGlobalScalarSquareIso f (pullback.snd f g) g (pullback.fst f g)
    pullback.condition).hom.naturality ((schemeDerivedGlobalSections (pullback f g)).map a)
  dsimp only [Functor.comp_map] at hs
  have hc := (mixedGlobalSectionsDirectImageIso (pullback.fst f g)).hom.naturality a
  dsimp only [Functor.comp_map] at hc
  have hc' := congrArg (fun k ↦ (schemeGlobalScalarRestriction f).map k) hc
  simp only [Functor.map_comp] at hc'
  simp only [Category.assoc] at hc' hu' ⊢
  rw [reassoc_of% hc', reassoc_of% hs, reassoc_of% hu']
  simp only [S, Functor.comp_obj, Category.comp_id]


end AlgebraicGeometry
