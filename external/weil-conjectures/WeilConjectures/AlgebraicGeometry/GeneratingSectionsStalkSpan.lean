/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Topology.Sheaves.Skyscraper
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Generating sections detected by the span of their germs

Source: Stacks Project, Modules, Definition 01AM; Sheaves, Lemma 0H7H(2).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private lemma freeHom_app_ι {Y : Scheme.{u}} (M : Y.Modules) {I : Type u}
    (s : I → M.sections) (i : I) (U : Y.Opens) (a : Y.presheaf.obj (Opposite.op U)) :
    Hom.app (M.freeHomEquiv.symm s) U
      (Hom.app (SheafOfModules.ιFree (R := Y.ringCatSheaf) i) U a) =
      a • ((s i).eval (Opposite.op U)) := by
  have h : SheafOfModules.ιFree i ≫ M.freeHomEquiv.symm s = M.unitHomEquiv.symm (s i) := by
    rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, Equiv.apply_symm_apply]
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, h]
  have ha : a = a • (1 : Y.presheaf.obj (Opposite.op U)) := (mul_one a).symm
  rw [ha, Hom.app_smul]
  congr 1
  exact congrArg (fun t : M.sections ↦ t.val (Opposite.op U))
    (M.unitHomEquiv.apply_symm_apply (s i))

set_option backward.isDefEq.respectTransparency false in
/-- Global sections generate a module exactly when their germs span every stalk.

Source: Stacks Project, Modules, Definition 01AM; Sheaves, Lemma 0H7H(2).
(blueprint: lem-weil-pbc-generating-sections-stalk-span).

Proof: The free sheaf morphism sends its i-th basis section to s i. The stalk map
is linear. For a finite family the identity on the free sheaf is the sum of the
basis inclusions composed with the coordinate projections. Representing any stalk
element by a section and applying this identity shows that the image of the stalk
map is contained in the span of the germs of s i. Conversely each germ of s i is
the image of the germ of the i-th basis section, so the image contains that span.
The forgetful functor to abelian sheaves preserves colimits, hence epimorphisms.
The stalk functor on abelian sheaves is a left adjoint, hence also preserves epis,
which are surjective in abelian groups. This proves the forward implication. For
the reverse implication, span equality makes each stalk map surjective, and the
stalk-surjectivity criterion makes the original module morphism an epimorphism.
The empty finite family is handled by the same identity with an empty sum; on an
empty scheme the pointwise conditions are vacuous. -/
theorem generating_sections_iff_stalk_span (Y : Scheme.{u}) (M : Y.Modules)
    {I : Type u} [Finite I] (s : I → M.sections) :
    Epi (M.freeHomEquiv.symm s) ↔ ∀ y : Y,
      Submodule.span (Y.presheaf.stalk y)
        (Set.range fun i ↦
          (TopCat.Presheaf.germ M.val.presheaf ⊤ y trivial)
            ((s i).val (Opposite.op ⊤))) = ⊤ := by
  classical
  let := Fintype.ofFinite I
  let f : SheafOfModules.free (R := Y.ringCatSheaf) I ⟶ M := M.freeHomEquiv.symm s
  have hr (y : Y) : LinearMap.range (Hom.stalkLinearMap f y) =
      Submodule.span (Y.presheaf.stalk y)
        (Set.range fun i ↦ (TopCat.Presheaf.germ M.val.presheaf ⊤ y trivial)
          ((s i).val (Opposite.op ⊤))) := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      obtain ⟨U, hy, t, rfl⟩ :=
        TopCat.Presheaf.exists_germ_eq
          (SheafOfModules.free (R := Y.ringCatSheaf) I).val.presheaf z
      have ht : t = ∑ i : I, Hom.app (SheafOfModules.ιFree (R := Y.ringCatSheaf) i) U
          (Hom.app (freeπ i) U t) := by
        have hh := Hom.sum_app_apply Finset.univ
          (fun i : I ↦ freeπ i ≫ SheafOfModules.ιFree (R := Y.ringCatSheaf) i) U t
        erw [sum_freeπ_ιFree, Hom.id_app] at hh
        simpa only [AddCommGrpCat.id_apply, Hom.comp_app,
          ConcreteCategory.comp_apply] using hh
      erw [Hom.stalkLinearMap_germ]
      rw [ht, map_sum, map_sum]
      apply Submodule.sum_mem
      intro i _
      rw [freeHom_app_ι]
      erw [germ_smul]
      have hs : (TopCat.Presheaf.germ M.val.presheaf U y hy) ((s i).val (Opposite.op U)) =
          (TopCat.Presheaf.germ M.val.presheaf ⊤ y trivial)
            ((s i).val (Opposite.op ⊤)) := by
        rw [← PresheafOfModules.sections_property (s i) (homOfLE le_top).op]
        exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
      erw [hs]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      refine ⟨(TopCat.Presheaf.germ
        (SheafOfModules.free (R := Y.ringCatSheaf) I).val.presheaf ⊤ y trivial)
          (Hom.app (SheafOfModules.ιFree (R := Y.ringCatSheaf) i) ⊤
            (1 : Y.presheaf.obj (Opposite.op ⊤))), ?_⟩
      erw [Hom.stalkLinearMap_germ]
      rw [freeHom_app_ι, one_smul]
      rfl
  constructor
  · intro h
    let : Epi f := h
    intro y
    let G := SheafOfModules.toSheaf Y.ringCatSheaf ⋙ (TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y)
    have : (TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).IsLeftAdjoint := inferInstance
    have : G.PreservesEpimorphisms := inferInstance
    have : Epi (G.map f) := inferInstance
    rw [← hr, LinearMap.range_eq_top]
    exact (AddCommGrpCat.epi_iff_surjective (G.map f)).mp inferInstance
  · intro h
    apply epi_of_surjective_stalk f
    intro y
    change Function.Surjective (Hom.stalkLinearMap f y)
    rw [← LinearMap.range_eq_top, hr]
    exact h y

end AlgebraicGeometry.Scheme.Modules
