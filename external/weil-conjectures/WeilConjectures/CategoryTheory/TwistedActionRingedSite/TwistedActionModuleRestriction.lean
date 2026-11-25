/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionModuleMorphismExtension
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionModuleObjectExtension

/-! # Modules on a fixed twisted action site

Source: the agent-formulated twisted variant of Stacks Tag 00W0, original steps 3 and 4.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.TwistedActionRingedSite

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (s : C ≌ C) [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    (R : Sheaf J CommRingCat.{u})
    (a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R)

omit [s.functor.IsContinuous J J] in
private theorem iso_of_two_composites {D : Type*} [Category D]
    {X Y : D} (f : X ⟶ Y) (g : Y ⟶ X) [IsIso (f ≫ g)] [IsIso (g ≫ f)] :
    IsIso f := by
  let r := g ≫ inv (f ≫ g)
  let l := inv (g ≫ f) ≫ g
  have hr : f ≫ r = 𝟙 X := by simp [r, ← Category.assoc]
  have hl : l ≫ f = 𝟙 Y := by simp [l, Category.assoc]
  have hlr : l = r := by
    calc
      l = l ≫ (f ≫ r) := by rw [hr, Category.comp_id]
      _ = r := by rw [← Category.assoc, hl, Category.id_comp]
  exact ⟨⟨r, hr, by rw [← hlr]; exact hl⟩⟩

variable (S : Site J s R a)

omit [s.functor.IsContinuous J J] in
private def generator (X : C) :
    letI := S.category
    S.inclusion.obj (s.inverse.obj X) ⟶ S.inclusion.obj X :=
  (S.arrows (s.inverse.obj X) X).symm ⟨-1, 𝟙 _⟩

omit [s.functor.IsContinuous J J] in
private theorem inclusion_arrow {X Y : C} (f : X ⟶ Y) :
    letI := S.category
    letI := S.inclusion_continuous
    S.inclusion.map f = (S.arrows X Y).symm ⟨0, f⟩ := by
  let := S.category
  let := S.inclusion_continuous
  apply (S.arrows X Y).injective
  simp only [S.arrows_inclusion, Equiv.apply_symm_apply]

omit [s.functor.IsContinuous J J] in
private theorem powerComp_neg_one_zero (X : C) :
    letI := S.category
    letI := S.inclusion_continuous
    (S.powerComp (-1) 0).hom.app X = 𝟙 (s.inverse.obj X) := by
  let := S.category
  let := S.inclusion_continuous
  have h := S.arrows_comp (s.inverse.obj X) X X (-1) 0 (𝟙 _) (𝟙 _)
  rw [← S.arrows_id X, Equiv.symm_apply_apply, Category.comp_id,
    Equiv.apply_symm_apply] at h
  simpa using (eq_of_heq (Sigma.mk.inj h).2).symm

omit [s.functor.IsContinuous J J] in
private theorem powerComp_zero_neg_one (X : C) :
    letI := S.category
    letI := S.inclusion_continuous
    (S.powerComp 0 (-1)).hom.app X = 𝟙 (s.inverse.obj X) := by
  let := S.category
  let := S.inclusion_continuous
  have h := S.arrows_comp (s.inverse.obj X) (s.inverse.obj X) X 0 (-1) (𝟙 _) (𝟙 _)
  rw [← S.arrows_id (s.inverse.obj X), Equiv.symm_apply_apply, Category.id_comp,
    Equiv.apply_symm_apply] at h
  simpa using (eq_of_heq (Sigma.mk.inj h).2).symm

omit [s.functor.IsContinuous J J] in
private theorem generator_naturality {X Y : C} (f : X ⟶ Y) :
    letI := S.category
    letI := S.inclusion_continuous
    S.inclusion.map (s.inverse.map f) ≫ generator J s R a S Y =
      generator J s R a S X ≫ S.inclusion.map f := by
  let := S.category
  let := S.inclusion_continuous
  apply (S.arrows (s.inverse.obj X) Y).injective
  rw [inclusion_arrow J s R a S, inclusion_arrow J s R a S]
  simp [generator, S.arrows_comp, powerComp_neg_one_zero, powerComp_zero_neg_one]

omit [s.functor.IsContinuous J J] in
private theorem generator_isIso (X : C) :
    letI := S.category
    IsIso (generator J s R a S X) := by
  let := S.category
  let := S.inclusion_continuous
  let g : S.inclusion.obj X ⟶ S.inclusion.obj (s.inverse.obj X) :=
    (S.arrows X (s.inverse.obj X)).symm ⟨1, s.counitIso.inv.app X⟩
  have h₁ : generator J s R a S X ≫ g = S.inclusion.map
      (s.inverse.map (s.counitIso.inv.app X) ≫ (S.powerComp (-1) 1).hom.app
        (s.inverse.obj X)) := by
    apply (S.arrows _ _).injective
    simp only [generator, g, S.arrows_comp, S.arrows_inclusion,
      Category.id_comp]
    rfl
  have h₂ : g ≫ generator J s R a S X = S.inclusion.map
      (s.counitIso.inv.app X ≫ (S.powerComp 1 (-1)).hom.app X) := by
    apply (S.arrows _ _).injective
    simp only [generator, g, S.arrows_comp, S.arrows_inclusion,
      Functor.map_id, Category.id_comp]
    rfl
  have : IsIso (generator J s R a S X ≫ g) := by rw [h₁]; infer_instance
  have : IsIso (g ≫ generator J s R a S X) := by rw [h₂]; infer_instance
  exact iso_of_two_composites _ g

omit [s.functor.IsContinuous J J] in
private noncomputable def generatorIso :
    letI := S.category
    s.inverse ⋙ S.inclusion ≅ S.inclusion := by
  letI := S.category
  letI := S.inclusion_continuous
  letI (X : C) := generator_isIso J s R a S X
  exact NatIso.ofComponents (fun X ↦ asIso (generator J s R a S X))
    (fun f ↦ generator_naturality J s R a S f)

omit [s.functor.IsContinuous J J] in
private noncomputable def restrictionFunctor :
    letI := S.category
    letI := S.inclusion_continuous
    Modules S.coefficient ⥤ Modules R := by
  letI := S.category
  letI := S.inclusion_continuous
  exact SheafOfModules.pushforward
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map S.coefficientRestriction.inv)

omit [s.functor.IsContinuous J J] in
private theorem coefficient_comparison :
    letI := S.category
    letI := S.inclusion_continuous
    letI := Functor.isContinuous_comp s.inverse S.inclusion J J S.topology
    (sheafCompose J (forget₂ CommRingCat RingCat)).map S.coefficientRestriction.inv ≫
      (Functor.sheafPushforwardContinuousNatTrans (generatorIso J s R a S).hom
        RingCat J S.topology).app (ring S.coefficient) =
    (sheafCompose J (forget₂ CommRingCat RingCat)).map a.inv ≫
      (s.inverse.sheafPushforwardContinuous RingCat J J).map
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map
          S.coefficientRestriction.inv) := by
  let := S.category
  let := S.inclusion_continuous
  let := Functor.isContinuous_comp s.inverse S.inclusion J J S.topology
  ext X r
  apply (ConcreteCategory.bijective_of_isIso
    (S.coefficientRestriction.hom.hom.app (op (s.inverse.obj X.unop)))).injective
  change (S.coefficientRestriction.hom.hom.app (op (s.inverse.obj X.unop)))
      (S.coefficient.obj.map
        ((S.arrows (s.inverse.obj X.unop) X.unop).symm ⟨-1, 𝟙 _⟩).op
        (S.coefficientRestriction.inv.hom.app X r)) =
    (S.coefficientRestriction.hom.hom.app (op (s.inverse.obj X.unop)))
      (S.coefficientRestriction.inv.hom.app (op (s.inverse.obj X.unop))
        (a.inv.hom.app X r))
  have h := S.coefficient_generator X.unop
    (S.coefficientRestriction.inv.hom.app X r)
  simpa only [← CommRingCat.comp_apply, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, CommRingCat.id_apply] using h

omit [s.functor.IsContinuous J J] in
private noncomputable def restrictionGenerator :
    letI := S.category
    letI := S.inclusion_continuous
    restrictionFunctor J s R a S ≅ restrictionFunctor J s R a S ⋙ sigma J s R a := by
  letI := S.category
  letI := S.inclusion_continuous
  letI := Functor.isContinuous_comp s.inverse S.inclusion J J S.topology
  let k := SheafOfModules.pushforwardCongr₂
    (F := s.inverse ⋙ S.inclusion) (G := S.inclusion)
    (T := ring R) (S := ring S.coefficient)
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map S.coefficientRestriction.inv)
    (generatorIso J s R a S) (coefficient_comparison J s R a S)
  let l := SheafOfModules.pushforwardComp
    (F := s.inverse) (G := S.inclusion) (S := ring R) (R := ring R)
    (R' := ring S.coefficient)
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map a.inv)
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map S.coefficientRestriction.inv)
  exact k ≪≫ l.symm

omit [s.functor.IsContinuous J J] in
private noncomputable def restrictionPairs :
    letI := S.category
    letI := S.inclusion_continuous
    Modules S.coefficient ⥤ Pairs (sigma J s R a) := by
  letI := S.category
  letI := S.inclusion_continuous
  exact {
    obj M := ⟨⟨(restrictionFunctor J s R a S).obj M,
      (restrictionGenerator J s R a S).inv.app M⟩, inferInstance⟩
    map f := ObjectProperty.homMk
      { f := (restrictionFunctor J s R a S).map f
        h := (restrictionGenerator J s R a S).inv.naturality f }
    map_id M := by
      apply ObjectProperty.hom_ext
      apply Endofunctor.Algebra.Hom.ext
      exact (restrictionFunctor J s R a S).map_id M
    map_comp f g := by
      apply ObjectProperty.hom_ext
      apply Endofunctor.Algebra.Hom.ext
      exact (restrictionFunctor J s R a S).map_comp f g
  }

omit [s.functor.IsContinuous J J] in
private theorem restriction_generator :
    letI := S.category
    letI := S.inclusion_continuous
    ∀ (M : Modules S.coefficient) (X : C)
    (x : ((sigma J s R a).obj ((restrictionPairs J s R a S).obj M).obj.a).val.obj
      (op X)),
    x = M.val.map ((S.arrows (s.inverse.obj X) X).symm ⟨-1, 𝟙 _⟩).op
      (((restrictionPairs J s R a S).obj M).obj.str.val.app (op X) x) := by
  let := S.category
  let := S.inclusion_continuous
  intro M X x
  have h := congrArg (fun f ↦ f.val.app (op X) x)
    ((restrictionGenerator J s R a S).inv_hom_id_app M)
  exact h.symm

omit [s.functor.IsContinuous J J] in
private theorem restriction_faithful :
    letI := S.category
    letI := S.inclusion_continuous
    (restrictionPairs J s R a S).Faithful := by
  let := S.category
  let := S.inclusion_continuous
  constructor
  intro M N f g h
  have he (X : C) : f.val.app (op (S.inclusion.obj X)) =
      g.val.app (op (S.inclusion.obj X)) := by
    ext x
    exact congrArg (fun k ↦ k.hom.f.val.app (op X) x) h
  ext X x
  have hX : S.inclusion.obj X.unop.base = X.unop := S.inclusion_obj X.unop.base
  have hh : f.val.app X = g.val.app X := by
    have hh := he X.unop.base
    rw [hX] at hh
    exact hh
  exact congrArg (fun k ↦ k x) hh

private theorem restriction_full :
    letI := S.category
    letI := S.inclusion_continuous
    (restrictionPairs J s R a S).Full := by
  let := S.category
  let := S.inclusion_continuous
  constructor
  intro M N f
  let h : (restrictionFunctor J s R a S).obj M ⟶
      (restrictionFunctor J s R a S).obj N := f.hom.f
  have hf : (sigma J s R a).map h ≫ (restrictionGenerator J s R a S).inv.app N =
      (restrictionGenerator J s R a S).inv.app M ≫ h := f.hom.h
  have hc : h ≫ (restrictionGenerator J s R a S).hom.app N =
      (restrictionGenerator J s R a S).hom.app M ≫ (sigma J s R a).map h := by
    apply (cancel_mono ((restrictionGenerator J s R a S).inv.app N)).1
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    rw [hf, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  obtain ⟨g, hg⟩ := moduleMorphismExtension J s R a S M N h (by
    intro X x
    exact congrArg (fun k ↦ k.val.app (op X) x) hc.symm)
  refine ⟨g, ?_⟩
  apply ObjectProperty.hom_ext
  apply Endofunctor.Algebra.Hom.ext
  exact hg

private theorem restriction_essSurj [HasPullbacks C] :
    letI := S.category
    letI := S.inclusion_continuous
    (restrictionPairs J s R a S).EssSurj := by
  let := S.category
  let := S.inclusion_continuous
  constructor
  intro P
  obtain ⟨N, b, hb⟩ := moduleObjectExtension J s R a S P
  have h : (sigma J s R a).map b.inv ≫
        (restrictionGenerator J s R a S).inv.app N = P.obj.str ≫ b.inv := by
    apply (cancel_mono ((restrictionGenerator J s R a S).hom.app N)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    ext X x
    exact hb X.unop x
  exact ⟨N, ⟨(ObjectProperty.isoMk _ (Endofunctor.Algebra.isoMk b.symm h)).symm⟩⟩

/-- Module restriction for a specified underlying twisted action site.

Source: original steps 3 and 4 of the agent-formulated twisted variant of Stacks 00W0,
`sites.tex`, proposition-sheaves-on-group, together with Stacks 03CV
(blueprint: lem-sf-twisted-action-module-restriction).

Proof: restrict a coefficient module to degree-zero arrows and transport its scalars
through coefficientRestriction. Apply its restriction along the minus-one generator,
then the inverse, to obtain the structure isomorphism for sigma. The coefficient
normalization says precisely that this is linear over a inverse. The category laws
give the intertwining equation for every module morphism. Conversely, iterate a
fixed pair's structure isomorphism for positive and negative powers to define the
restriction along every labelled arrow. Naturality, invertibility, and the power
comparisons give identity and composition. The generating-cover criterion in the
site construction identifies the sheaf conditions on C and on the action site, so
these extensions are sheaves of modules. These constructions are inverse, with
coefficient transport supplying the displayed natural restriction isomorphism.
On the minus-one generator they give exactly the displayed equation. Since every
map is the same family of sectionwise linear maps, restriction preserves sums.
The construction also holds for zero modules and the zero ring. No set-sheaf
presentation, geometric adjunction, or translation equivalence is asserted here. -/
theorem moduleRestriction [HasPullbacks C] (S : Site J s R a) :
    letI := S.category
    letI := S.inclusion_continuous
    ∃ (e : Modules S.coefficient ≌ Pairs (sigma J s R a))
      (c : e.functor ⋙ forgetPairs (sigma J s R a) ≅
        SheafOfModules.pushforward
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map S.coefficientRestriction.inv)),
      (∀ (M : Modules S.coefficient) (X : C)
        (x : ((sigma J s R a).obj (e.functor.obj M).obj.a).val.obj (op X)),
        (c.hom.app M).val.app (op (s.inverse.obj X)) x =
          M.val.map ((S.arrows (s.inverse.obj X) X).symm ⟨-1, 𝟙 _⟩).op
            ((c.hom.app M).val.app (op X)
              ((e.functor.obj M).obj.str.val.app (op X) x))) := by
  let := S.category
  let := S.inclusion_continuous
  let F := restrictionPairs J s R a S
  have : F.Faithful := restriction_faithful J s R a S
  have : F.Full := restriction_full J s R a S
  have : F.EssSurj := restriction_essSurj J s R a S
  have : F.IsEquivalence := {}
  refine ⟨F.asEquivalence, Iso.refl _, ?_⟩
  intro M X x
  exact restriction_generator J s R a S M X x

end CategoryTheory.TwistedActionRingedSite
