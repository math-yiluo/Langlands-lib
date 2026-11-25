/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Sites.LocalProperties

/-! # Cover-local detection of derived module isomorphisms

Source: Stacks Project, sites-cohomology.tex, Tag 0944, first locality sentence;
categories.tex, localization and cohomology criteria.
(blueprint: lem-weil-pbc-ringed-restriction-local-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

/-- Exact slice restriction detects derived isomorphisms on covering sieves.
Source: Stacks Project, sites-cohomology.tex, Tag 0944, first locality sentence.
(blueprint: lem-weil-pbc-ringed-restriction-local-iso).

Proof: choose a covering sieve on each object as in the hypothesis. The domains of
all arrows in these sieves form a family covering every object. Exact restriction
commutes with each cohomology functor, so every cohomology map is invertible after
restriction to this family. Forget to abelian sheaves, use the sheaf axiom to glue
local inverses, and reflect invertibility to modules. The unbounded derived
cohomology criterion concludes, degree by degree without a uniform bound. -/
theorem ringedRestrictionLocalIso
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r})
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{r}]
    [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasDerivedCategory.{w} (SheafOfModules.{r} R)]
    [∀ V : C, HasDerivedCategory.{w} (SheafOfModules.{r} (R.over V))]
    {A B : DerivedCategory (SheafOfModules.{r} R)} (a : A ⟶ B)
    (h : ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧
      ∀ (W : C) (f : W ⟶ V), S f →
        IsIso ((ringedDerivedRestrictionGeneral R W).map a)) : IsIso a := by
  classical
  choose S hS hi using h
  let I := Σ V : C, {f : Over V // S V f.hom}
  let W : I → C := fun i ↦ i.2.1.left
  have hW : J.CoversTop W := by
    intro V
    apply J.superset_covering _ (hS V)
    intro T f hf
    exact ⟨⟨V, ⟨Over.mk f, hf⟩⟩, ⟨𝟙 T⟩⟩
  apply (DerivedCategory.isIso_iff _ a).2
  intro n
  have : IsIso ((toSheaf R).map ((DerivedCategory.homologyFunctor _ n).map a)) := by
    apply Sheaf.isIso_of_coversTop hW
    intro i
    let F := overFunctor.{r} R (W i)
    have : F.Additive := (ringedOverFunctor_exactGeneral R (W i)).1
    have : PreservesFiniteLimits F := (ringedOverFunctor_exactGeneral R (W i)).2.1
    have : PreservesFiniteColimits F := (ringedOverFunctor_exactGeneral R (W i)).2.2
    have : IsIso (F.mapDerivedCategory.map a) := hi i.1 i.2.1.left i.2.1.hom i.2.2
    have : IsIso (F.map ((DerivedCategory.homologyFunctor _ n).map a)) :=
      (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) a).2
        (inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor _ n).map
          (F.mapDerivedCategory.map a))))
    change IsIso ((toSheaf (R.over (W i))).map
      (F.map ((DerivedCategory.homologyFunctor _ n).map a)))
    infer_instance
  exact isIso_of_reflects_iso _ (toSheaf R)

end SheafOfModules
