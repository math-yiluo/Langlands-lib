/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.CategoryTheory.InjectiveTowerRoos.InjectiveTowerRoosShifts
import WeilConjectures.CategoryTheory.Strict.StrictRoosHomotopyFunctor
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-! # The canonical Roos augmentation on arbitrary K-injective towers

Source: Stacks 0941 and 070I; extension from injective-term replacements by homotopy
equivalence (blueprint: lem-pur-kinjective-roos-augmentation).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe a b w r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The actual ordinary-limit augmentation is a quasi-isomorphism on every K-injective
tower, including towers whose terms are not injective.

Source: Stacks 0941, proof of lemma-derived-limit-is-ok, and 070I, comparison of
K-injective resolutions (blueprint: lem-pur-kinjective-roos-augmentation).

Proof: Resolve the supplied tower by a K-injective tower with injective terms. Since
both towers are K-injective, the resolution map is a homotopy equivalence. The additive
ordinary-limit functor preserves this equivalence; identify its complex-valued model
with the ordinary limit of evaluated complexes by the limit universal property.
The strict Roos homotopy functor preserves the same equivalence. The augmentation
on the injective-term target is a quasi-isomorphism by the split-transition/kernel
argument of Stacks 0941. Naturality gives the square with these two equivalences.
Two-out-of-three then proves the assertion for the supplied tower. This uses no
exactness assumption on products and applies to the zero tower as well. -/
theorem kInjectiveRoosAugmentation
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A]
    [IsGrothendieckAbelian.{r} (ℕᵒᵖ ⥤ A)]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
    QuasiIso (roosι I) := by
  let K := (CochainComplex.kInjectiveResolutionFunctor.{r} (ℕᵒᵖ ⥤ A)).obj I
  let v : I ⟶ K := (CochainComplex.toKInjectiveResolution.{r} (ℕᵒᵖ ⥤ A)).app I
  have hv : QuasiIso v :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{r} _ I).2
  have hK : QuasiIso (roosι K) := injective_roos_quasiIso K (fun _ ↦ inferInstance)
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff v).1 hv
  have hR : QuasiIso (roosF.map v) := by
    have hh := (roosF_homotopy_functor.{a, b, 0} (A := A)).2.1
    let eR : HomotopyEquiv (roosF.obj I) (roosF.obj K) :=
      { hom := roosF.map e.hom
        inv := roosF.map e.inv
        homotopyHomInvId := by
          simpa only [Functor.map_comp, Functor.map_id] using
            (hh _ _ _ _ e.homotopyHomInvId).choose
        homotopyInvHomId := by
          simpa only [Functor.map_comp, Functor.map_id] using
            (hh _ _ _ _ e.homotopyInvHomId).choose }
    simpa only [eR, he] using eR.quasiIso_hom
  let : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive := baseLimit_additive
  have hL : QuasiIso (roosLimitFunctor.map v) := by
    have hm : QuasiIso (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex
        (.up ℤ)).map v) := by
      simpa only [Functor.mapHomotopyEquiv_hom, he] using
        ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomotopyEquiv e).quasiIso_hom
    have hn := (limitModelIso (A := A)).hom.naturality v
    have heq : roosLimitFunctor.map v =
        (limitModelIso (A := A)).inv.app I ≫
          (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).map v) ≫
            (limitModelIso (A := A)).hom.app K := by
      simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using
        (congrArg (fun f ↦ (limitModelIso (A := A)).inv.app I ≫ f) hn).symm
    rw [heq]
    infer_instance
  have hc : QuasiIso (roosι I ≫ roosF.map v) := by
    rw [← roosι_natural]
    change QuasiIso (roosLimitFunctor.map v ≫ roosι K)
    infer_instance
  exact (quasiIso_iff_comp_right (roosι I) (roosF.map v)).1 hc

end CategoryTheory
