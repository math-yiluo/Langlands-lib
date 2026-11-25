/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.SitePerfectModelRestriction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.CategoryTheory.SiteRestrictionKInjective

/-! # K-injectives under relocalization

Source: Stacks Project, Cohomology on Sites, restriction of K-injectives to an open.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

/-- Relocalization preserves K-injectives, with an independent coefficient universe.
Source: Stacks Project, Cohomology on Sites, lemma-restrict-K-injective-to-open;
Modules on Sites, Tags 03DI and 03DJ.
(auxiliary; not a blueprint node).

Proof: Regard f as an object X of C/U. Restriction from C/U to (C/U)/X preserves
K-injectives by exact extension by zero. The iterated-slice equivalence identifies
(C/U)/X with C/V, and induces an additive equivalence of their module categories.
An additive equivalence preserves K-injectives. Its composite with restriction is
sectionwise the original relocalization functor, so transport the preservation
property through this identity comparison. The topology and coefficient sheaf on
the iterated slice agree with those transported from C/V.
-/
theorem overMap_preservesKInjectiveComplexes_ofUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{r}) {U V : C} (f : V ⟶ U)
    [HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    [hV : HasSheafify (J.over V) AddCommGrpCat.{max u v r}]
    [hWV : (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v r}] :
    (overMap.{max u v r} R f).PreservesKInjectiveComplexes := by
  let X : Over U := Over.mk f
  let : HasSheafify (J.over X.left) AddCommGrpCat.{max u v r} := hV
  let : (J.over X.left).WEqualsLocallyBijective AddCommGrpCat.{max u v r} := hWV
  let : HasSheafify ((J.over U).over X) AddCommGrpCat.{max u v r} :=
    X.iteratedSliceEquiv.hasSheafify ((J.over U).over X) (J.over X.left)
      AddCommGrpCat.{max u v r}
  let : ((J.over U).over X).WEqualsLocallyBijective AddCommGrpCat.{max u v r} :=
    GrothendieckTopology.WEqualsLocallyBijective.transport
      ((J.over U).over X) (J.over X.left) X.iteratedSliceEquiv.inverse
      (A := AddCommGrpCat.{max u v r})
      (Functor.IsDenseSubsite.coverPreserving (J.over X.left) ((J.over U).over X)
        X.iteratedSliceEquiv.inverse)
  let : Abelian (SheafOfModules.{max u v r} ((R.over U).over X)) :=
    instAbelian.{max u v r, v, r, max u v} ((R.over U).over X)
  let : Abelian (SheafOfModules.{max u v r} (R.over X.left)) :=
    instAbelian.{max u v r, v, r, max u v} (R.over X.left)
  let : Abelian (SheafOfModules.{max u v r} (R.over U)) :=
    instAbelian.{max u v r, v, r, max u v} (R.over U)
  let E₀ : SheafOfModules.{max u v r} (R.over X.left) ≌
      SheafOfModules.{max u v r} ((R.over U).over X) :=
    pushforwardPushforwardEquivalence X.iteratedSliceEquiv
      (S := (R.over U).over X) (R := R.over X.left) (𝟙 _) (𝟙 _)
      (by ext : 2; exact R.obj.map_id _) (by ext : 2; exact R.obj.map_id _)
  let E := E₀.symm
  let F := overFunctor.{max u v r} (R.over U) X
  have : F.PreservesKInjectiveComplexes :=
    overFunctor_preservesKInjectiveComplexes_ofUniverses.{max u v, v, r} (R.over U) X
  have : E.functor.Additive := ⟨by
    intro A B f g
    ext Y x
    rfl⟩
  have : E.functor.IsEquivalence := E.isEquivalence_functor
  have : E.functor.PreservesKInjectiveComplexes :=
    Functor.preservesKInjectiveComplexes_of_isEquivalence.{max u v r, max u v r,
      (max u v r) + 1, (max u v r) + 1} E.functor
  have : (F ⋙ E.functor).PreservesKInjectiveComplexes :=
    Functor.preservesKInjectiveComplexes_comp.{(max u v r) + 1, (max u v r) + 1,
      (max u v r) + 1, max u v r, max u v r, max u v r} F E.functor
  let e : F ⋙ E.functor ≅ overMap.{max u v r} R f :=
    NatIso.ofComponents
      (fun (M : SheafOfModules.{max u v r} (R.over U)) ↦ Iso.refl _) (by intros; rfl)
  exact Functor.preservesKInjectiveComplexes_of_iso.{(max u v r) + 1,
    (max u v r) + 1, max u v r, max u v r} e

end SheafOfModules
