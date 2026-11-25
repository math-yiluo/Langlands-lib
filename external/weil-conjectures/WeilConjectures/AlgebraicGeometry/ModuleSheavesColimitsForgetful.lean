/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Colimits of sheaves of modules and the forgetful functor

Source: Stacks Project, Modules on Sites, Lemmas 03DA, 03DB, 03CO and 03CY
(blueprint: situation-conventions).
-/

@[expose] public section

universe u v u' v'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Source: Stacks Project, Modules on Sites, Lemmas 03DA, 03DB, 03CO and 03CY
(blueprint: situation-conventions).
The forgetful functor from module sheaves to abelian sheaves is faithful and exact.
Small limits exist and are sectionwise; small colimits exist and are the module
sheafifications of sectionwise presheaf colimits, with the canonical coprojections.
The forgetful functor preserves both. Small here means relative to the module universe `v'`.

Proof, following the four steps of the node:
1. By `situation-conventions`, form limits sectionwise, with
componentwise operations and restrictions. Their underlying abelian presheaves are the
sectionwise limits, which are sheaves and limits in abelian sheaves by
`situation-conventions` (1). Thus forgetting preserves limits.
2. By `situation-conventions`, form the presheaf colimit
`P`, with its module structure and coprojections. Apply the module sheafification of
`def-weil-presheaf-modules-sheafification`. A cocone into a module sheaf factors uniquely
through `P`, and then uniquely through its sheafification by the sheafification adjunction.
Uniqueness of both factorizations proves the colimit property, with coprojections induced
by the sheafification unit, as in `def-weil-pbc-category-colimit`.
3. Forgetting the module structure of `P` gives the presheaf colimit in abelian groups.
Module sheafification has the same underlying abelian sheaf as abelian sheafification
(`def-weil-pbc-sheafification`). The same two universal properties show that the resulting
abelian cocone is a colimit. Thus forgetting preserves colimits, including coprojections.
4. Morphisms are componentwise linear maps of abelian sheaves, so forgetting is faithful
and additive (`situation-conventions`). Kernels are limits of a map and zero;
cokernels are colimits of a map and zero. Steps 1 and 3 preserve these, and hence preserve
images and exact sequences in the abelian categories, as in `def-pur-abelian-sheaf-kernel`.
Equivalently, the forgetful functor preserves finite limits and finite colimits. -/
theorem moduleSheaves_colimits_forgetful
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u'})
    [HasSheafify J AddCommGrpCat.{v'}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v'}] :
    (SheafOfModules.toSheaf.{v'} R).Faithful ∧
      PreservesFiniteLimits (SheafOfModules.toSheaf.{v'} R) ∧
      PreservesFiniteColimits (SheafOfModules.toSheaf.{v'} R) ∧
      HasLimitsOfSize.{v', v'} (SheafOfModules.{v'} R) ∧
      HasColimitsOfSize.{v', v'} (SheafOfModules.{v'} R) ∧
      (∀ (K : Type v') [SmallCategory K],
        PreservesLimitsOfShape K (SheafOfModules.toSheaf.{v'} R) ∧
          PreservesColimitsOfShape K (SheafOfModules.toSheaf.{v'} R) ∧
          (∀ X : Cᵒᵖ, PreservesLimitsOfShape K (SheafOfModules.evaluation.{v'} R X)) ∧
          (∀ F : K ⥤ SheafOfModules.{v'} R,
            ∃ s : Cocone F, Nonempty (IsColimit s) ∧
              ∃ e : s.pt ≅ (PresheafOfModules.sheafification.{v'} (𝟙 R.obj)).obj
                  (PresheafOfModules.colimitPresheafOfModules (F ⋙ SheafOfModules.forget R)),
                ∀ i : K,
                  (PresheafOfModules.toPresheaf R.obj).map ((s.ι.app i).val ≫ e.hom.val) =
                    (PresheafOfModules.toPresheaf R.obj).map
                        ((PresheafOfModules.colimitCocone
                          (F ⋙ SheafOfModules.forget R)).ι.app i) ≫
                      toSheafify J
                        (PresheafOfModules.colimitPresheafOfModules
                          (F ⋙ SheafOfModules.forget R)).presheaf)) := by
  classical
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro K _
  have : PreservesLimitsOfShape K
      (SheafOfModules.toSheaf.{v'} R ⋙ sheafToPresheaf J AddCommGrpCat.{v'}) :=
    inferInstanceAs (PreservesLimitsOfShape K
      (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj))
  have : PreservesLimitsOfShape K (SheafOfModules.toSheaf.{v'} R) :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J AddCommGrpCat.{v'})
  refine ⟨inferInstance, inferInstance, fun X ↦ inferInstance, ?_⟩
  intro F
  let L := PresheafOfModules.sheafification.{v'} (𝟙 R.obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{v'} (𝟙 R.obj)
  let c := PresheafOfModules.colimitCocone (F ⋙ SheafOfModules.forget R)
  let e : F ≅ (F ⋙ SheafOfModules.forget R) ⋙ L :=
    Functor.isoWhiskerLeft F (asIso adj.counit).symm
  let s := (Cocone.precompose e.hom).obj (L.mapCocone c)
  refine ⟨s, ⟨?_⟩, Iso.refl _, ?_⟩
  · exact (IsColimit.precomposeHomEquiv e _).symm
      (isColimitOfPreserves L (PresheafOfModules.isColimitColimitCocone _))
  · intro i
    simp only [s, Cocone.precompose_obj_ι, Functor.mapCocone_ι_app,
      NatTrans.comp_app, Iso.refl_hom]
    have hunit : (e.hom.app i).val =
        adj.unit.app ((SheafOfModules.forget R).obj (F.obj i)) := by
      have : IsIso (adj.counit.app (F.obj i)).val :=
        inferInstanceAs (IsIso ((SheafOfModules.forget R).map
          (adj.counit.app (F.obj i))))
      apply (cancel_mono (adj.counit.app (F.obj i)).val).1
      have h := congrArg SheafOfModules.Hom.val
        ((asIso adj.counit).inv_hom_id_app (F.obj i))
      exact h.trans (adj.right_triangle_components (F.obj i)).symm
    simp only [SheafOfModules.comp_val, SheafOfModules.id_val,
      hunit, Functor.map_comp]
    change (PresheafOfModules.toPresheaf R.obj).map
        (adj.unit.app ((SheafOfModules.forget R).obj (F.obj i)) ≫
          (SheafOfModules.forget R).map (L.map (c.ι.app i))) = _
    erw [← adj.unit.naturality (c.ι.app i), Functor.map_comp]
    simp only [adj, PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    rfl


end CategoryTheory
