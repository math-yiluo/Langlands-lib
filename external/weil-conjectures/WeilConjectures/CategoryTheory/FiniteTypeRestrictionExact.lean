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
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-! # Exact restriction of module sheaves to a slice

Source: Stacks Project, Modules on Sites, Tag 093U (3), localization step.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Restricting modules on a small ringed site to a slice is exact.
Source: Stacks Project, Modules on Sites, Tag 093U (3), localization step.
(auxiliary; not a blueprint node).

Proof: The underlying abelian sheaf of a restricted module is its restricted underlying
abelian sheaf. Restriction of abelian sheaves preserves finite limits sectionwise and
preserves colimits because it is left adjoint to the pushforward along the cocontinuous
slice forgetful functor. The faithful exact forgetful functor from modules to abelian
sheaves reflects short exactness. Thus module restriction preserves short exact
sequences. The exact-functor criterion gives preservation of finite limits and colimits. -/
theorem overFunctor_exact {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) (U : C) :
    PreservesFiniteLimits (overFunctor.{u} R U) ∧
      PreservesFiniteColimits (overFunctor.{u} R U) := by
  let F := SheafOfModules.overFunctor.{u} R U
  have : F.Additive := ⟨fun {_ _} f g ↦ by ext V x; rfl⟩
  let e : F ⋙ SheafOfModules.toSheaf.{u} (R.over U) ≅
      SheafOfModules.toSheaf.{u} R ⋙ J.overPullback AddCommGrpCat.{u} U := Iso.refl _
  have : PreservesFiniteLimits (J.overPullback AddCommGrpCat.{u} U) := inferInstance
  have : PreservesFiniteColimits (J.overPullback AddCommGrpCat.{u} U) := inferInstance
  have h (S : ShortComplex (SheafOfModules.{u} R)) (hS : S.ShortExact) :
      (S.map F).ShortExact := by
    apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful
      (SheafOfModules.toSheaf.{u} (R.over U))
    exact ShortComplex.shortExact_of_iso (S.mapNatIso e.symm)
      ((hS.map_of_exact (SheafOfModules.toSheaf.{u} R)).map_of_exact
        (J.overPullback AddCommGrpCat.{u} U))
  exact (Functor.exact_tfae F).out 1 4 |>.mp h

end SheafOfModules
