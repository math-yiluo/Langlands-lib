/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientTransition

/-! # Uniqueness of the ordinary quotient arrows

A consecutive arrow of fixed-scalar coordinates is determined by its values on sheafified pure
tensors, since these generate every section locally.

Source: Stacks Project, Tags 03CY and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t v₀ u₀ u v₁ u₁
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {R₁ R₂ : Sheaf J CommRingCat.{u}} (α : R₁ ⟶ R₂) (M : SheafOfModules.{u} (𝓡 R₁))
  {Y : SheafOfModules.{u} (𝓡 R₂)} (h : Y = changeOfRings α M)

/-- Every section of a change of rings is, locally for a cocontinuous functor, a sheafified
section of sectionwise change of rings. -/
theorem changeOfRings_exists_local_presheaf {C' : Type u₁} [Category.{v₁} C']
    (J' : GrothendieckTopology C') (G : C' ⥤ C) [G.IsCocontinuous J' J] (U : C')
    (x : Y.val.obj (op (G.obj U))) :
    ∃ s ∈ J' U, ∀ ⦃V : C'⦄ (i : V ⟶ U), s i →
      ∃ p : (changeOfRingsPresheaf α M).obj (op (G.obj V)),
        Y.val.map (G.map i).op x = (eqToHom h.symm).val.app _
          ((toSheafify J (changeOfRingsPresheaf α M).presheaf).app _ p) := by
  subst h
  refine ⟨(Presheaf.imageSieve (toSheafify J (changeOfRingsPresheaf α M).presheaf)
    x).functorPullback G, G.cover_lift J' J
      (Presheaf.imageSieve_mem J (toSheafify J (changeOfRingsPresheaf α M).presheaf) x), ?_⟩
  intro V i hi
  obtain ⟨p, hp⟩ := hi
  exact ⟨p, hp.symm⟩

/-- Two additive maps out of a change of rings agree on sheafified sections of sectionwise
change of rings once they agree on sheafified pure tensors. -/
theorem changeOfRings_addHom_ext_tmul {T : Type*} [AddCommGroup T] (W : Cᵒᵖ)
    (F₁ F₂ : Y.val.obj W →+ T)
    (hF : ∀ (s : R₂.obj.obj W) (m : M.val.obj W),
      F₁ ((eqToHom h.symm).val.app W ((toSheafify J (changeOfRingsPresheaf α M).presheaf).app W
        (s ⊗ₜ[R₁.obj.obj W,(α.hom.app W).hom] m))) =
      F₂ ((eqToHom h.symm).val.app W ((toSheafify J (changeOfRingsPresheaf α M).presheaf).app W
        (s ⊗ₜ[R₁.obj.obj W,(α.hom.app W).hom] m))))
    (p : (changeOfRingsPresheaf α M).obj W) :
    F₁ ((eqToHom h.symm).val.app W
        ((toSheafify J (changeOfRingsPresheaf α M).presheaf).app W p)) =
      F₂ ((eqToHom h.symm).val.app W
        ((toSheafify J (changeOfRingsPresheaf α M).presheaf).app W p)) := by
  subst h
  change F₁ ((toSheafify J (changeOfRingsPresheaf α M).presheaf).app W p) =
    F₂ ((toSheafify J (changeOfRingsPresheaf α M).presheaf).app W p)
  induction p using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s m => exact hF s m

end SheafOfModules

namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Two morphisms of sheaves of modules agree if every section is locally sent to the same
section by both. -/
theorem sheafModuleHom_ext_of_local {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Type*} [Ring R] {S T : Sheaf J (ModuleCat.{t + 1} R)}
    [J.HasSheafCompose (CategoryTheory.forget (ModuleCat.{t + 1} R))] (f g : S ⟶ T)
    (h : ∀ (U : Cᵒᵖ) (x : S.obj.obj U), ∃ s ∈ J U.unop, ∀ ⦃V : C⦄ (i : V ⟶ U.unop), s i →
      f.hom.app (op V) (S.obj.map i.op x) = g.hom.app (op V) (S.obj.map i.op x)) :
    f = g := by
  have hs := (isSheaf_iff_isSheaf_of_type J
      (T.obj ⋙ CategoryTheory.forget (ModuleCat.{t + 1} R))).1
    ((sheafCompose J (CategoryTheory.forget (ModuleCat.{t + 1} R))).obj T).property
  apply Sheaf.hom_ext
  ext U x
  obtain ⟨s, hsJ, hx⟩ := h U x
  apply (hs.isSeparated _ hsJ).ext
  intro V i hi
  change T.obj.map i.op (f.hom.app U x) = T.obj.map i.op (g.hom.app U x)
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← f.hom.naturality, ← g.hom.naturality]
  exact hx i hi

/-- The consecutive arrows of fixed-scalar coordinates normalized on sheafified pure tensors
are unique.
Source: Stacks Project, Tags 03CY and 09C6.

Proof: every section of an ordinary scalar extension is locally the sheafification of a finite
sum of pure tensors. The localization functor of the chart is cocontinuous, so the sections
over charts are locally of that form within the chart site. Both arrows are additive and
agree on pure tensors, hence on these local generators; the target is a sheaf. -/
theorem finitePerfectAdicQuotientTransition_unique
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (V : X.Etale) (n : ℕ)
    (δ δ' : finitePerfectAdicQuotientStrictCoordinates X d φ V (n + 1) ⟶
      finitePerfectAdicQuotientStrictCoordinates X d φ V n ⋙
        finitePerfectAdicStepRestrict X d V n)
    (hδ : FinitePerfectAdicQuotientTransition X d φ V n δ)
    (hδ' : FinitePerfectAdicQuotientTransition X d φ V n δ') : δ = δ' := by
  ext N : 2
  apply sheafModuleHom_ext_of_local
  intro U x
  let G := MorphismProperty.Over.map ⊤ (show WeaklyEtale V.hom from inferInstance)
  let ψ := completedAdicCommProjection X d (n + 1)
  have : G.IsCocontinuous (ProEt.topology V.left) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap (show WeaklyEtale V.hom from inferInstance)
  obtain ⟨s, hs, hloc⟩ := SheafOfModules.changeOfRings_exists_local_presheaf ψ N
    ((completedAdicChangeData X ψ).choose_spec.choose N) (ProEt.topology V.left) G U.unop x
  refine ⟨s, hs, ?_⟩
  intro V' i hi
  obtain ⟨p, hp⟩ := hloc i hi
  let T := ((finitePerfectAdicQuotientStrictCoordinates X d φ V n ⋙
    finitePerfectAdicStepRestrict X d V n).obj N).obj.obj (op V')
  let F₁ : ((completedAdicChangeData X ψ).choose.obj N).val.obj (op (G.obj V')) →+ T :=
    ((δ.app N).hom.app (op V')).hom.toAddMonoidHom
  let F₂ : ((completedAdicChangeData X ψ).choose.obj N).val.obj (op (G.obj V')) →+ T :=
    ((δ'.app N).hom.app (op V')).hom.toAddMonoidHom
  have key := SheafOfModules.changeOfRings_addHom_ext_tmul ψ N
    ((completedAdicChangeData X ψ).choose_spec.choose N) (op (G.obj V')) F₁ F₂
    (fun b m ↦ (hδ N V' b m).trans (hδ' N V' b m).symm) p
  exact (congrArg F₁ hp).trans (key.trans (congrArg F₂ hp).symm)

end AlgebraicGeometry.Scheme
