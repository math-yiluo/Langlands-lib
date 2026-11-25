/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono
public import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Local lifting through an open counit

## References

* Stacks Project, Tags 00WK and 09AE
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

private theorem preimage_of_covering_imageSieve
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G : Sheaf J (Type (u + 1))} (f : F ⟶ G)
    (hf : ∀ Z, Function.Injective (f.hom.app Z)) {Q : C}
    (s : G.obj.obj (op Q)) (h : Presheaf.imageSieve f.hom s ∈ J Q) :
    ∃ t, f.hom.app (op Q) t = s := by
  classical
  have H := (isSheaf_iff_isSheaf_of_type J F.obj).mp F.property _ h
  let t : Presieve.FamilyOfElements F.obj (Presheaf.imageSieve f.hom s).arrows :=
    fun _ g hg ↦ Presheaf.localPreimage f.hom s g hg
  have ht : t.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ w
    apply hf
    have eq₁ := NatTrans.naturality_apply f.hom g₁.op (t f₁ hf₁)
    have eq₂ := NatTrans.naturality_apply f.hom g₂.op (t f₂ hf₂)
    have eq₃ := congrArg (G.obj.map g₁.op) (Presheaf.app_localPreimage f.hom s _ hf₁)
    have eq₄ := congrArg (G.obj.map g₂.op) (Presheaf.app_localPreimage f.hom s _ hf₂)
    refine eq₁.trans (eq₃.trans (Eq.trans ?_ (eq₄.symm.trans eq₂.symm)))
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    simp only [← op_comp, w]
  refine ⟨H.amalgamate t ht, ?_⟩
  apply (((isSheaf_iff_isSheaf_of_type J G.obj).mp G.property).isSeparated _ h).ext
  intro Y g hg
  rw [← NatTrans.naturality_apply, H.valid_glue ht]
  exact Presheaf.app_localPreimage f.hom s g hg

private theorem openCounit_mono (R : Type (u + 1)) [Ring R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) :
    Mono ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) j).counit.app F) := by
  apply mono_of_mono_openImmersionLowerShriekAdjunction_unit_app_comp
  rw [Adjunction.right_triangle_components]
  exact ⟨fun _ _ h ↦ by simpa using h⟩

/-- The open counit is invertible on a test object that factors through the open. -/
theorem isIso_openCounit_app_of_factors (R : Type (u + 1)) [Ring R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) (Q : X.ProEt)
    (hQ : ∃ g : Q.left ⟶ U, g ≫ j = Q.hom) :
    IsIso
      (((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) j).counit.app F).hom.app
        (op Q)) := by
  obtain ⟨g, hg⟩ := hQ
  have : WeaklyEtale (g ≫ j) := hg.symm ▸ Q.prop
  have : WeaklyEtale g := WeaklyEtale.of_comp g j
  let Q' : U.ProEt := ProEt.mk g
  let e : (openImmersionLocalization j).obj Q' ≅ Q :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by simpa [Q'] using hg.symm)
  let c := (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) j).counit.app F
  have hc : IsIso (c.hom.app (op ((openImmersionLocalization j).obj Q'))) :=
    inferInstanceAs (IsIso
      (((openImmersionRestriction (ModuleCat.{u + 1} R) j).map c).hom.app (op Q')))
  have hcQ : IsIso (c.hom.app (op Q)) := by
    have h := c.hom.naturality e.inv.op
    exact IsIso.of_isIso_fac_left h
  exact hcQ

/-- A section lifts through an open counit if it is locally zero or its test object
factors through the open. The counit is monic by the presheaf zero-extension formula
and exact sheafification. Its restriction to the open is invertible by the triangle
identity. Thus all the local sections lift, their lifts agree by monicity, and the
sheaf condition glues them, including for the empty covering. -/
theorem openCounit_section_lift (R : Type (u + 1)) [Ring R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) (Q : X.ProEt)
    (s : F.obj.obj (op Q)) (S : Sieve Q) (hS : S ∈ ProEt.topology X Q)
    (h : ∀ (Z : X.ProEt) (f : Z ⟶ Q), S f →
      (∃ g : Z.left ⟶ U, g ≫ j = Z.hom) ∨ F.obj.map f.op s = 0) :
    ∃ t, ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) j).counit.app F).hom.app
      (op Q) t = s := by
  let c := (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) j).counit.app F
  have : Mono c := openCounit_mono R j F
  let forgetSheaf := sheafCompose (ProEt.topology X) (forget (ModuleCat.{u + 1} R))
  apply preimage_of_covering_imageSieve (forgetSheaf.map c)
    (fun Z ↦ (ModuleCat.mono_iff_injective (c.hom.app Z)).mp inferInstance) s
  apply (ProEt.topology X).superset_covering _ hS
  intro Z f hf
  rcases h Z f hf with hZ | hz
  · have := isIso_openCounit_app_of_factors R j F Z hZ
    exact (ConcreteCategory.bijective_of_isIso (c.hom.app (op Z))).surjective
      (F.obj.map f.op s)
  · refine ⟨(0 : ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).obj
        ((openImmersionRestriction (ModuleCat.{u + 1} R) j).obj F)).obj.obj (op Z)), ?_⟩
    exact (map_zero (c.hom.app (op Z)).hom).trans hz.symm

end AlgebraicGeometry.ProEtale
