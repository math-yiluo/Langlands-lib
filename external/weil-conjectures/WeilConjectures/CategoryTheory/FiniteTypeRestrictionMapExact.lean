/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Exact further restriction of module sheaves between slices

Source: Stacks Project, Modules on Sites, Tag 093U (3), localization step.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Further restriction between slices of a small ringed site is exact.
Source: Stacks Project, Modules on Sites, Tag 093U (3), relocalization step.
(auxiliary; not a blueprint node).

Proof: On underlying abelian sheaves this is precomposition by the functor between the
slice categories. This functor is both continuous and cocontinuous for the slice
topologies. Its sheaf restriction is therefore a right adjoint and also a left adjoint,
so it preserves finite limits and colimits. The faithful exact forgetful functor reflects
short exact sequences. The exact-functor criterion gives the result for module sheaves. -/
theorem overMap_exact {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
    {X Y : C} (f : X ⟶ Y) :
    PreservesFiniteLimits (overMap.{u} R f) ∧
      PreservesFiniteColimits (overMap.{u} R f) := by
  let F := overMap.{u} R f
  let H := J.overMapPullback AddCommGrpCat.{u} f
  have : F.Additive := ⟨fun {_ _} a b ↦ by ext V x; rfl⟩
  let e : F ⋙ toSheaf.{u} (R.over X) ≅ toSheaf.{u} (R.over Y) ⋙ H := Iso.refl _
  have : PreservesFiniteLimits H := inferInstance
  have : PreservesColimitsOfSize.{u, u} H :=
    ((Over.map f).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
      (J.over X) (J.over Y)).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits H :=
    PreservesColimitsOfSize.preservesFiniteColimits H
  have h (S : ShortComplex (SheafOfModules.{u} (R.over Y))) (hS : S.ShortExact) :
      (S.map F).ShortExact := by
    apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful
      (toSheaf.{u} (R.over X))
    exact ShortComplex.shortExact_of_iso (S.mapNatIso e.symm)
      ((hS.map_of_exact (toSheaf.{u} (R.over Y))).map_of_exact H)
  exact (Functor.exact_tfae F).out 1 4 |>.mp h

end SheafOfModules
