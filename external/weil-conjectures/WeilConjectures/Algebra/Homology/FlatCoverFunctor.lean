/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Functorial flat covers of module sheaves

Source: Stacks Project, Modules on Sites, Lemma 03EW (3), (4)
(blueprint: lem-pc-sites-modules-functorial-flat-cover).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Module sheaves admit a functorial epimorphism from a flat module sheaf.

Source: Stacks Project, Modules on Sites, Lemma 03EW (3), (4)
(blueprint: lem-pc-sites-modules-functorial-flat-cover).

Proof: Forget a module sheaf to a presheaf, take the free module presheaf on
its underlying presheaf of sets, and sheafify. Evaluation on a free generator
is its indexing section, so the presheaf counit is sectionwise surjective.
Sheafification preserves epimorphisms, and its counit on a sheaf is an
isomorphism, so the composite augmentation is epic. Each section module
of the free presheaf is free and hence flat. Evaluation preserves and
jointly reflects limits, so sectionwise flatness shows its tensor functor
preserves finite limits. Apply `isFlat_sheafification_obj` (Stacks 03ET)
to obtain a flat sheaf. The free functor and sheafification are functors;
their counits give the natural augmentation. This is the sheafification
route allowed by the last sentence of the proof of 03EW. -/
theorem exists_functorial_flat_cover
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) :
    let A := SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    ∃ T : A ⥤ A, ∃ π : T ⟶ 𝟭 A,
      ∀ M : A, IsFlat (T.obj M) ∧ Epi (π.app M) := by
  let O := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let a := PresheafOfModules.sheafification (𝟙 O.obj)
  let V := SheafOfModules.forget O ⋙ PresheafOfModules.restrictScalars (𝟙 O.obj)
  let U := PresheafOfModules.toPresheaf O.obj ⋙
    (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget Ab)
  let G := U ⋙ PresheafOfModules.free O.obj
  let τ : G ⟶ 𝟭 _ :=
    { app := fun M ↦ PresheafOfModules.freeObjDesc (𝟙 _)
      naturality := by
        intro M M' f
        ext X : 1
        apply ModuleCat.free_hom_ext
        intro x
        change ModuleCat.freeDesc (↾fun x : M'.obj X ↦ x)
            ((ModuleCat.free (O.obj.obj X)).map (↾fun x ↦ f.app X x)
              (ModuleCat.freeMk x)) =
          f.app X (ModuleCat.freeDesc (↾fun x : M.obj X ↦ x) (ModuleCat.freeMk x))
        rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
        rfl }
  have hτ (M : PresheafOfModules.{u} O.obj) : Epi (τ.app M) := by
    apply PresheafOfModules.epi_of_surjective
    intro X x
    refine ⟨ModuleCat.freeMk x, ?_⟩
    change ModuleCat.freeDesc (↾fun x : M.obj X ↦ x) (ModuleCat.freeMk x) = x
    exact ModuleCat.freeDesc_apply _ _
  let T := V ⋙ G ⋙ a
  let π : T ⟶ 𝟭 _ :=
    Functor.whiskerLeft V (Functor.whiskerRight τ a) ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).counit
  refine ⟨T, π, fun M ↦ ⟨?_, ?_⟩⟩
  · have hflat : PreservesFiniteLimits
        (MonoidalCategory.tensorRight (G.obj (V.obj M))) := by
      constructor
      intro K hK hfin
      constructor
      intro F
      constructor
      intro c hc
      have hflatX (X : Cᵒᵖ) : Module.Flat (R.obj.obj X) ((G.obj (V.obj M)).obj X) := by
        change Module.Flat (R.obj.obj X) (_ →₀ R.obj.obj X)
        infer_instance
      have hpres (X : Cᵒᵖ) : PreservesFiniteLimits
          (MonoidalCategory.tensorRight
            (show ModuleCat (R.obj.obj X) from (G.obj (V.obj M)).obj X)) := by
        have := hflatX X
        infer_instance
      exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦
        isLimitOfPreserves (MonoidalCategory.tensorRight
          (show ModuleCat (R.obj.obj X) from (G.obj (V.obj M)).obj X))
            (isLimitOfPreserves (PresheafOfModules.evaluation _ X) hc))⟩
    have hid : IsIso (𝟙 O.obj) := inferInstance
    have hinj : Presheaf.IsLocallyInjective J (𝟙 O.obj) := inferInstance
    have hsurj : Presheaf.IsLocallySurjective J (𝟙 O.obj) := inferInstance
    exact (PresheafOfModules.isFlat_sheafification_obj (R := R)
      (𝟙 O.obj) (G.obj (V.obj M)) hflat).2
  · have := hτ (V.obj M)
    dsimp [π]
    infer_instance

end SheafOfModules
