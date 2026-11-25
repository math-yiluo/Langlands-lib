/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.RingTheory.Ideal.Span
public import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.FiniteSectionsEpiLift
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Local linear expressions in finite generating sections

Source: Stacks Project, Modules on Sites, finite type modules, and algebraization Tag 099E.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Opposite
open scoped BigOperators
namespace SheafOfModules

/-- A finite family of local sections is locally a linear combination of any finite family
of global generating sections, on one common covering sieve.
Source: Stacks Project, Tag 099E, equality of the section ideals after refinement.
(auxiliary; not a blueprint node).

Proof: lift the chosen sections simultaneously through the epimorphism from the finite
free module sheaf. Express each lifted free section in its finite coordinate basis and
apply the epimorphism. The image of the i-th basis section is the i-th generator. -/
theorem exists_cover_linearCombination_generators
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R)
    (σ : M.GeneratingSections) [Fintype σ.I] (U : C)
    {T : Type u} [Finite T] (s : T → M.val.obj (op U)) :
    ∃ S ∈ J U, ∀ (V : C) (a : V ⟶ U), S a →
      ∀ j, ∃ c : σ.I → R.obj.obj (op V),
        M.val.map a.op (s j) = ∑ i, c i • (show M.val.obj (op V) from (σ.s i).val (op V)) := by
  classical
  obtain ⟨S, hS, h⟩ := exists_cover_lift_finite_sections σ.π U s
  refine ⟨S, hS, ?_⟩
  intro V a ha j
  obtain ⟨x, hx⟩ := h V a ha j
  let c := freeSectionsLinearEquiv (R := R) σ.I (op V) x
  refine ⟨c, ?_⟩
  have hd := (freeSectionsLinearEquiv (R := R) σ.I (op V)).left_inv x
  change (∑ i, (ιFree (R := R) i).val.app (op V) (c i)) = x at hd
  rw [← hx, ← hd, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (ιFree i ≫ σ.π).val.app (op V) (c i) = _
  have hi : ιFree i ≫ σ.π = M.unitHomEquiv.symm (σ.s i) := by
    rw [← unitHomEquiv_symm_freeHomEquiv_apply]
    congr 1
    exact congrFun (M.freeHomEquiv.apply_symm_apply σ.s) i
  rw [hi]
  rfl

end SheafOfModules
