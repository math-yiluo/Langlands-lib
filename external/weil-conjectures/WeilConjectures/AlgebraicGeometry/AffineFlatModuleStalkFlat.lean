/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.Algebra.Category.ModuleCat.FilteredColimitFlat

/-! # Flat stalks from flat sections on affine subopens

Source: Stacks Project, Modules Tag 05NE, Algebra Tags 00H9 and 00HT.
(blueprint: lem-pc-affine-flat-module-stalk-flat).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Flat sections on all affine subopens give flatness of an individual stalk.
Source: Stacks Project, Modules Tag 05NE; Algebra Tags 00H9 and 00HT.
(blueprint: lem-pc-affine-flat-module-stalk-flat).

Proof: Choose an affine neighbourhood V of x. The affine neighbourhoods U of x
contained in V form a filtered basis: intersections are open, and each neighbourhood
contains an affine neighbourhood of x. Restrict scalars on G(U) along O(V) -> O(U).
The hypothesis gives flatness over O(V) for every such U. Germ maps identify their
filtered colimit with G_x as an O(V)-module; this uses only the neighbourhood-basis
property, not quasi-coherence. Filtered colimits of flat modules are flat (Tag 00H9).
The ring O_x is the localization of O(V) at the prime corresponding to x. The
O(V)-action just constructed is restriction of the canonical O_x-action, by the
formula for multiplication of germs. For a module over a localization, flatness over
the original ring is equivalent to flatness over the localization (Tag 00HT).
Consequently G_x is flat over O_x. There is no point to consider on the empty scheme;
for the zero sheaf this argument gives the zero, hence flat, stalk module. -/
theorem flat_stalk_of_affineFlatOver_identity {Y : Scheme.{u}} (G : Y.Modules)
    (hflat : Scheme.Modules.IsFlatOver G (𝟙 Y)) (x : Y) :
    Module.Flat (Y.toRingedSpace.presheaf.stalk x)
      ((RingedSpace.moduleStalkFunctor Y.toRingedSpace x).obj G) := by
  open CategoryTheory.Limits Opposite TopologicalSpace in
    set_option backward.isDefEq.respectTransparency false in
      classical
      obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
        (X := Y) (x := x) (U := ⊤) (by trivial)
      let A := Γ(Y, V)
      let S := Y.presheaf.stalk x
      let M := (RingedSpace.moduleStalkFunctor Y.toRingedSpace x).obj G
      let : Algebra A S := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨x, hxV⟩
      let : Module A M := Module.compHom M (algebraMap A S)
      have : IsScalarTower A S M := IsScalarTower.of_compHom A S M
      have := hV.isLocalization_stalk ⟨x, hxV⟩
      apply (Module.flat_iff_of_isLocalization S (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
        M).mpr
      let N := { U : OpenNhds x // IsAffineOpen U.1 ∧ U.1 ≤ V }
      have : Nonempty N := ⟨⟨⟨V, hxV⟩, hV, le_rfl⟩⟩
      have : IsCofiltered N :=
        { cone_objs := by
            intro U W
            obtain ⟨T, hT, hxT, hTUW⟩ := exists_isAffineOpen_mem_and_subset
              (show x ∈ U.1.1 ⊓ W.1.1 from ⟨U.1.2, W.1.2⟩)
            let t : N := ⟨⟨T, hxT⟩, hT, (hTUW.trans inf_le_left).trans U.2.2⟩
            exact ⟨t, homOfLE (hTUW.trans inf_le_left),
              homOfLE (hTUW.trans inf_le_right), trivial⟩
          cone_maps := fun {_ _} _ _ ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩ }
      let J : Nᵒᵖ ⥤ (OpenNhds x)ᵒᵖ :=
        { obj := fun U ↦ op U.unop.1
          map := fun f ↦ (homOfLE f.unop.le).op }
      have : J.Final := by
        apply Functor.final_of_exists_of_isFiltered
        · intro U
          obtain ⟨T, hT, hxT, hTU⟩ := exists_isAffineOpen_mem_and_subset
            (show x ∈ U.unop.1 ⊓ V from ⟨U.unop.2, hxV⟩)
          exact ⟨op ⟨⟨T, hxT⟩, hT, hTU.trans inf_le_right⟩,
            ⟨(homOfLE (hTU.trans inf_le_left)).op⟩⟩
        · intro U W f g
          exact ⟨W, 𝟙 _, Subsingleton.elim _ _⟩
      let stageModule (U : Nᵒᵖ) : Module A (G.val.obj (op U.unop.1.1)) :=
        Module.compHom _ (Y.presheaf.map (homOfLE U.unop.2.2).op).hom
      let Q (U : Nᵒᵖ) : ModuleCat.{u} A := ModuleCat.of A (G.val.obj (op U.unop.1.1))
      let F : Nᵒᵖ ⥤ ModuleCat.{u} A :=
        { obj := Q
          map := fun {U W} f ↦ ModuleCat.ofHom
            { toFun := G.val.map
                (homOfLE f.unop.le : W.unop.1.1 ⟶ U.unop.1.1).op
              map_add' := fun a b ↦ map_add (G.val.presheaf.map
                (homOfLE f.unop.le : W.unop.1.1 ⟶ U.unop.1.1).op).hom a b
              map_smul' := by
                intro a m
                change G.val.map (homOfLE f.unop.le : W.unop.1.1 ⟶ U.unop.1.1).op
                  ((Y.presheaf.map (homOfLE U.unop.2.2).op).hom a • m) =
                  (Y.presheaf.map (homOfLE W.unop.2.2).op).hom a •
                    (show G.val.obj (op W.unop.1.1) from
                      G.val.map (homOfLE f.unop.le : W.unop.1.1 ⟶ U.unop.1.1).op m)
                rw [G.val.map_smul]
                congr 1
                change (Y.presheaf.map (homOfLE f.unop.le).op).hom
                  ((Y.presheaf.map (homOfLE U.unop.2.2).op).hom a) =
                    (Y.presheaf.map (homOfLE W.unop.2.2).op).hom a
                rw [← CommRingCat.comp_apply, ← Y.presheaf.map_comp]
                rfl }
          map_id := by
            intro U
            ext m
            change G.val.presheaf.map (𝟙 _) m = m
            simp
          map_comp := by intro U W T f g; ext m; exact G.val.map_comp_apply _ _ _ }
      let c : Cocone F :=
        { pt := ModuleCat.of A M
          ι :=
            { app := fun U ↦ ModuleCat.ofHom
                { toFun := TopCat.Presheaf.germ G.val.presheaf U.unop.1.1 x U.unop.1.2
                  map_add' := fun a b ↦ map_add _ a b
                  map_smul' := by
                    intro a m
                    change TopCat.Presheaf.germ G.val.presheaf U.unop.1.1 x U.unop.1.2
                      ((Y.presheaf.map (homOfLE U.unop.2.2).op).hom a • m) =
                        (Y.presheaf.germ V x hxV).hom a •
                          TopCat.Presheaf.germ G.val.presheaf U.unop.1.1 x U.unop.1.2 m
                    rw [PresheafOfModules.germ_smul (R := Y.presheaf)]
                    rw [TopCat.Presheaf.germ_res_apply] }
              naturality := by
                intro U W f
                ext m
                exact TopCat.Presheaf.germ_res_apply G.val.presheaf
                  (homOfLE f.unop.le) x W.unop.1.2 m } }
      have hc : IsColimit c := by
        apply isColimitOfReflects (forget₂ (ModuleCat A) AddCommGrpCat)
        change IsColimit ((colimit.cocone ((OpenNhds.inclusion x).op ⋙ G.val.presheaf)).whisker J)
        exact (Functor.Final.isColimitWhiskerEquiv J _).symm (colimit.isColimit _)
      have hf (U : Nᵒᵖ) : Module.Flat A (F.obj U) := by
        have e : U.unop.1.1 ≤ (𝟙 Y : Y ⟶ Y) ⁻¹ᵁ V := by simpa using U.unop.2.2
        have h := hflat ⟨V, hV⟩ ⟨U.unop.1.1, U.unop.2.1⟩ e
        have heq : (𝟙 Y : Y ⟶ Y).appLE V U.unop.1.1 e =
            Y.presheaf.map (homOfLE U.unop.2.2).op := by
          simp [Scheme.Hom.appLE]
        dsimp only at h
        rw [heq] at h
        exact h
      have : Module.Flat A (colimit F : ModuleCat A) := ModuleCat.filteredColimit_flat F hf
      let e : c.pt ≅ colimit F := hc.coconePointUniqueUpToIso (colimit.isColimit F)
      exact Module.Flat.of_linearEquiv e.toLinearEquiv

end AlgebraicGeometry
