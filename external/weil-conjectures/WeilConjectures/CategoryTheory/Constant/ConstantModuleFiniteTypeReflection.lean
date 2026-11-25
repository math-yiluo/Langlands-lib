/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.CategoryTheory.Sites.EpiMono

/-! # Constant module sheaves reflect finite generation

Source: Stacks Project, Modules on Sites, Tag 093N, assertion (1)
(blueprint: lem-sfb-constant-module-finite-type-reflection).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory.Limits Opposite
open scoped BigOperators

namespace CategoryTheory

private abbrev cmod {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (B : Type (max u v)) [CommRing B] (M : ModuleCat.{max u v} B) :=
  (siteConstantModuleFunctorGeneral J B).obj M

private abbrev cunit {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (B : Type (max u v)) [CommRing B] (M : ModuleCat.{max u v} B)
    : (Functor.const Cᵒᵖ).obj ((forget₂ (ModuleCat B) AddCommGrpCat).obj M) ⟶
      (cmod J B M).val.presheaf :=
  toSheafify J ((siteConstantModulePresheafGeneral (C := C) B).obj M).presheaf

private lemma local_span
    {D : Type u} [Category.{v} D] {J : GrothendieckTopology D}
    {R : Sheaf J RingCat.{max u v}} (F : SheafOfModules.{max u v} R)
    (σ : F.GeneratingSections) [Fintype σ.I] (U : D) (s : F.val.obj (op U)) :
    ∃ S ∈ J U, ∀ (V : D) (a : V ⟶ U), S a →
      ∃ c : σ.I → R.obj.obj (op V),
        F.val.map a.op s = ∑ i, c i •
          (show F.val.obj (op V) from (σ.s i).val (op V)) := by
  classical
  let φ := (SheafOfModules.toSheaf R).map σ.π
  have : Epi φ := inferInstance
  have : Sheaf.IsLocallySurjective φ := (Sheaf.isLocallySurjective_iff_epi' _ φ).2
    inferInstance
  have : Presheaf.IsLocallySurjective J φ.hom := inferInstance
  refine ⟨Presheaf.imageSieve φ.hom s, Presheaf.imageSieve_mem J φ.hom s, ?_⟩
  intro V a ha
  obtain ⟨x, hx⟩ := ha
  change σ.π.val.app (op V) x = F.val.map a.op s at hx
  let c := SheafOfModules.freeSectionsLinearEquiv (R := R) σ.I (op V) x
  refine ⟨c, ?_⟩
  have hd := (SheafOfModules.freeSectionsLinearEquiv (R := R) σ.I (op V)).left_inv x
  change (∑ i, (SheafOfModules.ιFree (R := R) i).val.app (op V) (c i)) = x at hd
  rw [← hx, ← hd, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (SheafOfModules.ιFree i ≫ σ.π).val.app (op V) (c i) = _
  have hi : SheafOfModules.ιFree i ≫ σ.π = F.unitHomEquiv.symm (σ.s i) := by
    rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    congr 1
    exact congrFun (F.freeHomEquiv.apply_symm_apply σ.s) i
  rw [hi]
  rfl

-- Elaborating slice restriction and the module-sheafification unit needs this budget.
end CategoryTheory
