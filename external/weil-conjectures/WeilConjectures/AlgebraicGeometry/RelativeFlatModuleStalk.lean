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

/-! # Relative flatness on stalks

Source: Stacks Project, Morphisms, Tag 01U2, and Algebra, Tags 00H9 and 00HT.
(blueprint: lem-pc-relative-flat-module-stalk).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Affine-local relative flatness implies flatness of the module stalk over the base stalk.
Source: Stacks Project, Morphisms Tag 01U2; Algebra Tags 00H9 and 00HT.
(blueprint: lem-pc-relative-flat-module-stalk).

Proof: Choose an affine neighbourhood V of f(x). Affine neighbourhoods U of x inside
f⁻¹(V) form a filtered neighbourhood basis. The hypothesis makes every G(U) flat
over O(V); their filtered colimit G_x is therefore flat over O(V). Its scalar action
factors through O_{S,f(x)}, the localization of O(V) at f(x), because the scalar
multiplication of germs agrees with the stalk map of f. Flatness over a ring and
over its localization are equivalent for a module over the latter. The equation
hRA identifies the chosen algebra structure with that stalk map. Empty schemes
have no point x; the zero sheaf gives the flat zero stalk. -/
theorem relative_flat_module_stalk {S X : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) (hflat : G.IsFlatOver f) (x : X)
    [Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x)]
    (hRA : algebraMap (S.presheaf.stalk (f x)) (X.presheaf.stalk x) = (f.stalkMap x).hom) :
    Module.Flat (S.presheaf.stalk (f x))
      ((ModuleCat.restrictScalars (algebraMap (S.presheaf.stalk (f x))
        (X.presheaf.stalk x))).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G)) := by
  open CategoryTheory.Limits Opposite TopologicalSpace in
    set_option backward.isDefEq.respectTransparency false in
      classical
      obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
        (X := S) (x := f x) (U := ⊤) (by trivial)
      let A := Γ(S, V)
      let R := S.presheaf.stalk (f x)
      let M := (ModuleCat.restrictScalars (algebraMap R (X.presheaf.stalk x))).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G)
      let : Algebra A R := TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨f x, hxV⟩
      let : Module A M := Module.compHom M (algebraMap A R)
      have : IsScalarTower A R M := IsScalarTower.of_compHom A R M
      have := hV.isLocalization_stalk ⟨f x, hxV⟩
      apply (Module.flat_iff_of_isLocalization R (hV.primeIdealOf ⟨f x, hxV⟩).asIdeal.primeCompl
        M).mpr
      let N := { U : OpenNhds x // IsAffineOpen U.1 ∧ U.1 ≤ f ⁻¹ᵁ V }
      have : Nonempty N := by
        obtain ⟨U, hU, hxU, he⟩ := exists_isAffineOpen_mem_and_subset
          (X := X) (x := x) (U := f ⁻¹ᵁ V) hxV
        exact ⟨⟨⟨U, hxU⟩, hU, he⟩⟩
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
          map := fun a ↦ (homOfLE a.unop.le).op }
      have : J.Final := by
        apply Functor.final_of_exists_of_isFiltered
        · intro U
          obtain ⟨T, hT, hxT, hTU⟩ := exists_isAffineOpen_mem_and_subset
            (show x ∈ U.unop.1 ⊓ (f ⁻¹ᵁ V) from ⟨U.unop.2, hxV⟩)
          exact ⟨op ⟨⟨T, hxT⟩, hT, hTU.trans inf_le_right⟩,
            ⟨(homOfLE (hTU.trans inf_le_left)).op⟩⟩
        · intro U W a b
          exact ⟨W, 𝟙 _, Subsingleton.elim _ _⟩
      let stageModule (U : Nᵒᵖ) : Module A (G.val.obj (op U.unop.1.1)) :=
        Module.compHom _ (f.appLE V U.unop.1.1 U.unop.2.2).hom
      let Q (U : Nᵒᵖ) : ModuleCat.{u} A := ModuleCat.of A (G.val.obj (op U.unop.1.1))
      let F : Nᵒᵖ ⥤ ModuleCat.{u} A :=
        { obj := Q
          map := fun {U W} a ↦ ModuleCat.ofHom
            { toFun := G.val.map
                (homOfLE a.unop.le : W.unop.1.1 ⟶ U.unop.1.1).op
              map_add' := fun m n ↦ map_add (G.val.presheaf.map
                (homOfLE a.unop.le : W.unop.1.1 ⟶ U.unop.1.1).op).hom m n
              map_smul' := by
                intro r m
                change G.val.map (homOfLE a.unop.le : W.unop.1.1 ⟶ U.unop.1.1).op
                  ((f.appLE V U.unop.1.1 U.unop.2.2).hom r • m) =
                    (f.appLE V W.unop.1.1 W.unop.2.2).hom r •
                      (show G.val.obj (op W.unop.1.1) from
                        G.val.map (homOfLE a.unop.le : W.unop.1.1 ⟶ U.unop.1.1).op m)
                rw [G.val.map_smul]
                congr 1
                exact congrArg (fun k : Γ(S, V) ⟶ Γ(X, W.unop.1.1) ↦ k r)
                  (f.appLE_map U.unop.2.2 (homOfLE a.unop.le).op) }
          map_id := by
            intro U
            ext m
            change G.val.presheaf.map (𝟙 _) m = m
            simp
          map_comp := by intro U W T a b; ext m; exact G.val.map_comp_apply _ _ _ }
      let c : Cocone F :=
        { pt := ModuleCat.of A M
          ι :=
            { app := fun U ↦ ModuleCat.ofHom
                { toFun := TopCat.Presheaf.germ G.val.presheaf U.unop.1.1 x U.unop.1.2
                  map_add' := fun m n ↦ map_add _ m n
                  map_smul' := by
                    intro r m
                    change TopCat.Presheaf.germ G.val.presheaf U.unop.1.1 x U.unop.1.2
                      ((f.appLE V U.unop.1.1 U.unop.2.2).hom r • m) =
                        algebraMap R (X.presheaf.stalk x) ((S.presheaf.germ V (f x) hxV).hom r)
                          • TopCat.Presheaf.germ G.val.presheaf U.unop.1.1 x U.unop.1.2 m
                    rw [hRA, f.germ_stalkMap_apply,
                      PresheafOfModules.germ_smul (R := X.presheaf)]
                    congr 1
                    exact TopCat.Presheaf.germ_res_apply X.presheaf
                      (homOfLE U.unop.2.2) x U.unop.1.2 (f.app V r) }
              naturality := by
                intro U W a
                ext m
                exact TopCat.Presheaf.germ_res_apply G.val.presheaf
                  (homOfLE a.unop.le) x W.unop.1.2 m } }
      have hc : IsColimit c := by
        apply isColimitOfReflects (forget₂ (ModuleCat A) AddCommGrpCat)
        change IsColimit ((colimit.cocone ((OpenNhds.inclusion x).op ⋙ G.val.presheaf)).whisker J)
        exact (Functor.Final.isColimitWhiskerEquiv J _).symm (colimit.isColimit _)
      have hf (U : Nᵒᵖ) : Module.Flat A (F.obj U) :=
        hflat ⟨V, hV⟩ ⟨U.unop.1.1, U.unop.2.1⟩ U.unop.2.2
      have : Module.Flat A (colimit F : ModuleCat A) := ModuleCat.filteredColimit_flat F hf
      let e : c.pt ≅ colimit F := hc.coconePointUniqueUpToIso (colimit.isColimit F)
      exact Module.Flat.of_linearEquiv e.toLinearEquiv

end AlgebraicGeometry
