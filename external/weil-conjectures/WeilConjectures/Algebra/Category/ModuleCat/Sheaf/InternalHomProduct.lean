/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Internal Hom preserves products in its second argument

Source: Stacks Project, Modules on Sites, Section 03EK and Lemma 03EO.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

set_option backward.isDefEq.respectTransparency false in
/-- Apply internal Hom from a fixed module sheaf to a product fan.
Source: Stacks Project, Modules on Sites, Section internal-hom and
Lemma internal-hom-adjoint-tensor (03EO).
(blueprint: lem-sc-internal-hom-product-fan).

Proof: Products of module sheaves are computed sectionwise. Restrict the product
fan to the slice over U; it is still a product, since at each slice object its
components are the original sectionwise product. A family of localized maps
A to N_i therefore lifts uniquely to a localized map A to the product. Taking
these lifts defines the components of a map to internal Hom. Projection
uniqueness proves additivity, scalar compatibility, and compatibility with
restriction, so these components form a sheaf-module morphism. The same
uniqueness proves the factorization and uniqueness clauses of the product fan.
This uses no finiteness or local freeness; zero factors cause no exception. -/
theorem internalHomProductFanIsLimit (A : Mod) (N : ℤ → Mod)
    (c : Fan N) (hc : IsLimit c) :
    Nonempty (IsLimit (Fan.mk (homObj (R := R) A c.pt)
      (fun i ↦ homObjMap (R := R) (𝟙 A) (c.proj i))))  := by
  classical
  let F (U : C) := SheafOfModules.forget
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⋙
      PresheafOfModules.restrictOver R.obj U
  have hU (U : C) : IsLimit ((F U).mapCone c) := by
    apply PresheafOfModules.evaluationJointlyReflectsLimits
    intro W
    exact isLimitOfPreserves (SheafOfModules.evaluation _ (op W.unop.left)) hc
  let t := Fan.mk (homObj (R := R) A c.pt)
    (fun i ↦ homObjMap (R := R) (𝟙 A) (c.proj i))
  refine ⟨isLimitOfReflects (SheafOfModules.forget _) ?_⟩
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro U
  let d := Fan.mk ((PresheafOfModules.restrictOver R.obj U.unop).obj c.pt.val)
    (fun i ↦ (PresheafOfModules.restrictOver R.obj U.unop).map (c.proj i).val)
  have hd : IsLimit d := (Fan.isLimitMapConeEquiv (F U.unop) N c) (hU U.unop)
  change IsLimit ((SheafOfModules.evaluation _ U).mapCone t)
  refine (Fan.isLimitMapConeEquiv (SheafOfModules.evaluation _ U) _ t).symm ?_
  refine Fan.IsLimit.mk _ (fun s ↦ ModuleCat.ofHom
    (Y := (homObj (R := R) A c.pt).val.obj U)
    { toFun := fun x ↦ Fan.IsLimit.lift hd (fun i ↦ (s.proj i).hom x)
      map_add' := ?_
      map_smul' := ?_ }) ?_ ?_
  · intro x y
    apply Fan.IsLimit.hom_ext hd
    intro i
    rw [Fan.IsLimit.fac, Preadditive.add_comp, Fan.IsLimit.fac, Fan.IsLimit.fac]
    exact (s.proj i).hom.map_add x y
  · intro r x
    apply Fan.IsLimit.hom_ext hd
    intro i
    rw [Fan.IsLimit.fac]
    rw [PresheafOfModules.smul_eq_comp_sectionsSMul, Category.assoc,
      ← PresheafOfModules.sectionsSMul_naturality, ← Category.assoc,
      Fan.IsLimit.fac]
    exact (s.proj i).hom.map_smul r x
  · intro s i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (𝟙 _ ≫ Fan.IsLimit.lift hd (fun j ↦ (s.proj j).hom x)) ≫ d.proj i = _
    rw [Category.id_comp]
    exact Fan.IsLimit.fac hd (fun j ↦ (s.proj j).hom x) i
  · intro s f hf
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Fan.IsLimit.hom_ext hd
    intro i
    change f.hom x ≫ d.proj i =
      Fan.IsLimit.lift hd (fun j ↦ (s.proj j).hom x) ≫ d.proj i
    rw [Fan.IsLimit.fac]
    have hi := congrArg
      (fun z : s.pt ⟶ (homObj (R := R) A (N i)).val.obj U ↦ z.hom x) (hf i)
    change (𝟙 _ ≫ f.hom x) ≫ d.proj i = (s.proj i).hom x at hi
    simpa only [Category.id_comp] using hi

end SheafOfModules
