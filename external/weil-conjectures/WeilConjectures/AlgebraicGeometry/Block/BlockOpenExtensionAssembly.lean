/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.System.SystemBlockConstructions
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.Open.OpenRestrictionEvaluationSections
import WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearSystemIsoAssembly
import WeilConjectures.AlgebraicGeometry.Block.BlockOpenExtensionTransitions

/-! # Assembly and normalization of the block open-extension comparison
Source: Zheng Construction 4.1; Stacks 03DI--03DJ.
(blueprint: lem-pur-block-open-extension-assembly)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe c v r u₁ u₂ u₃ v₁ v₂ v₃ w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
private theorem systemHom_ext
    {C' : Type c} [Category.{v} C'] (K : GrothendieckTopology C')
    [EssentiallySmall.{max c v r} C']
    (B' : ℕ → Sheaf K CommRingCat.{max c v r})
    (τ' : ∀ n : ℕ, B' (n + 1) ⟶ B' n)
    {M N : Systems K B' τ'} {f g : M ⟶ N}
    (h : ∀ n, (evaluation K B' τ' n).map f = (evaluation K B' τ' n).map g) :
    f = g := by
  ext V x
  exact congrArg (fun k ↦ k.val.app (op V.unop.2) x) (h V.unop.1)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] evaluation systemRing ringPresheaf rings in
private theorem systemNatIsoOfEvaluation
    {D : Type u₁} [Category.{v₁} D]
    {C' : Type c} [Category.{v} C'] (K : GrothendieckTopology C')
    [EssentiallySmall.{max c v r} C']
    (B' : ℕ → Sheaf K CommRingCat.{max c v r})
    (τ' : ∀ n : ℕ, B' (n + 1) ⟶ B' n)
    (F H : D ⥤ Systems K B' τ')
    (δ : ∀ n : ℕ, F ⋙ evaluation K B' τ' n ≅ H ⋙ evaluation K B' τ' n)
    (ht : ∀ P {m n : ℕ} (h : n ≤ m),
      (transition K B' τ' h).app (F.obj P) ≫
          (res (coefficientMap K B' τ' h)).map ((δ n).hom.app P) =
        (δ m).hom.app P ≫ (transition K B' τ' h).app (H.obj P)) :
    ∃ ξ : F ≅ H, ∀ P n,
      (evaluation K B' τ' n).map (ξ.hom.app P) = (δ n).hom.app P := by
  classical
  have hex (P : D) : ∃ e : F.obj P ≅ H.obj P, ∀ n,
      (evaluation K B' τ' n).map e.hom = (δ n).hom.app P := by
    refine systemIsoOfEvaluation_exists.{c, v, r} K B' τ'
      (M := F.obj P) (N := H.obj P) (fun n ↦ (δ n).app P) ?_
    intro m n h
    simpa only [Iso.app_hom, Functor.comp_obj] using ht P h
  choose e he using hex
  let ξ : F ≅ H := NatIso.ofComponents e (by
    intro P P' f
    apply systemHom_ext.{c, v, r} K B' τ'
    intro n
    rw [Functor.map_comp, Functor.map_comp, he, he]
    exact (δ n).hom.naturality f)
  exact ⟨ξ, he⟩

private theorem eqToIsoSections
    {D₀ : Type u₁} {D₁ : Type u₂} [Category.{v₁} D₀] [Category.{v₂} D₁]
    {K : GrothendieckTopology D₁} {S : Sheaf K RingCat.{w}}
    {F H : D₀ ⥤ SheafOfModules.{w} S} (h : F = H)
    (M : D₀) (V : D₁ᵒᵖ) (x : (F.obj M).val.obj V) :
    HEq ((((eqToIso h).hom.app M).val.app V) x) x := by
  subst H
  rfl

private theorem mappedEquality_heq
    {D₀ : Type u₁} {D₁ : Type u₂} {D₂ : Type u₃}
    [Category.{v₁} D₀] [Category.{v₂} D₁] [Category.{v₃} D₂]
    (H : D₁ ⥤ D₂) {F G : D₀ ⥤ D₁} (h : F = G) (P : D₀)
    {X : D₂} (f : X ⟶ H.obj (F.obj P)) :
    HEq (f ≫ H.map ((eqToIso h).hom.app P)) f := by
  subst G
  change HEq (f ≫ H.map (𝟙 (F.obj P))) f
  rw [H.map_id, Category.comp_id]

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B₀ : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ₀ : ∀ n : ℕ, B₀ (n + 1) ⟶ B₀ n) (t : SystemBlockMap) (U : C)

private theorem normalizedOpenSystems :
    ∃ O : OpenSystems.{c, v, r} J B₀ τ₀ U,
      ∀ (n : ℕ) N V x,
        HEq (((O.restrictionEvaluation n).hom.app N).val.app V x) x := by
  classical
  let O := (semilinearDerivedSections.{c, v, r} J B₀ τ₀).some.localization U
  let a (n : ℕ) := @SheafOfModules.localizedSystemAdjunction.{c, v, r} C _ J
    (abelianSheafify.{c, v, max c v r} J)
    (locallyBijective.{c, v, max c v r} J) (B₀ n) U
  let δ (n : ℕ) := (openRestrictionEvaluationSections.{c, v, r} J B₀ τ₀ U n).choose
  have : ((𝟭 ℕ).prod (Over.forget U)).IsContinuous
      (coefficientSequenceTopology (J.over U)) (coefficientSequenceTopology J) :=
    openSite_continuous J U
  have hi (n : ℕ) :
      IsIso ((mateEquiv O.ordinaryAdjunction (a n)).symm (δ n).hom) := by
    apply WeilConjectures.SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso
      (J.over U) J (Over.forget U)
      (ring.{max c v, v, max c v r} (coefficientSequenceTopology (J.over U))
        (systemRing.{max c v, v, max c v r} (J.over U)
          (openRings.{c, v, r} J B₀ U) (openTransitions.{c, v, r} J B₀ τ₀ U)))
      (ring.{c, v, max c v r} (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J B₀ τ₀)) n
      (eqToHom (openRing.{c, v, r} J B₀ τ₀ U).symm)
      (ring.{max c v, v, max c v r} (J.over U) ((B₀ n).over U))
      (ring.{c, v, max c v r} J (B₀ n))
      (evaluation_ring.{max c v, v, max c v r} (J.over U)
        (openRings.{c, v, r} J B₀ U) (openTransitions.{c, v, r} J B₀ τ₀ U) n)
      (evaluation_ring.{c, v, max c v r} J B₀ τ₀ n) (𝟙 _)
      O.extension _ O.ordinaryAdjunction (a n) (δ n)
  let ι (n : ℕ) :=
    (asIso ((mateEquiv O.ordinaryAdjunction (a n)).symm (δ n).hom)).symm
  refine ⟨{ O with
    extensionEvaluation := ι
    restrictionEvaluation := δ
    restrictionSections := fun n N V x ↦
      (openRestrictionEvaluationSections.{c, v, r} J B₀ τ₀ U n).choose_spec N V.unop x
    unit_evaluation := ?_
    counit_evaluation := ?_ }, ?_⟩
  · intro n M
    have h := unit_mateEquiv_symm O.ordinaryAdjunction (a n) (δ n).hom M
    change _ ≫ _ ≫ _ = _
    rw [reassoc_of% h, ← Functor.map_comp]
    change (a n).unit.app _ ≫
      (SheafOfModules.localizedSystemRestriction.{c, v, r} (B₀ n) U).map
        ((asIso ((mateEquiv O.ordinaryAdjunction (a n)).symm (δ n).hom)).hom.app M ≫
          (asIso ((mateEquiv O.ordinaryAdjunction (a n)).symm (δ n).hom)).inv.app M) = _
    rw [Iso.hom_inv_id_app]
    erw [(SheafOfModules.localizedSystemRestriction.{c, v, r} (B₀ n) U).map_id,
      Category.comp_id]
  · intro n N
    exact mateEquiv_counit_symm O.ordinaryAdjunction (a n) (δ n).hom N
  · intro n N V x
    exact (openRestrictionEvaluationSections.{c, v, r} J B₀ τ₀ U n).choose_spec N V.unop x

attribute [local irreducible] evaluation systemRing ringPresheaf rings in
private theorem component_normalization
    (R : SystemBlockRepetition J B₀ τ₀ t)
    (Q : Systems (J.over U) (openRings.{c, v, r} J B₀ U)
        (openTransitions.{c, v, r} J B₀ τ₀ U) ⥤
      Systems (J.over U) (openRings.{c, v, r} J (blockCoefficients B₀ t) U)
        (openTransitions.{c, v, r} J (blockCoefficients B₀ t)
          (blockTransitions J B₀ τ₀ t) U))
    (qequal : ∀ m : ℕ,
      Q ⋙ evaluation (J.over U) (openRings.{c, v, r} J (blockCoefficients B₀ t) U)
          (openTransitions.{c, v, r} J (blockCoefficients B₀ t)
            (blockTransitions J B₀ τ₀ t) U) m =
        evaluation (J.over U) (openRings.{c, v, r} J B₀ U)
          (openTransitions.{c, v, r} J B₀ τ₀ U) (t.index m))
    (O : OpenSystems.{c, v, r} J B₀ τ₀ U)
    (OD : OpenSystems.{c, v, r} J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t) U)
    (m : ℕ) (P : Systems (J.over U) (openRings.{c, v, r} J B₀ U)
      (openTransitions.{c, v, r} J B₀ τ₀ U)) :
    HEq ((blockOpenExtensionComponent.{c, v, r} J B₀ τ₀ t U R Q
          (fun n ↦ eqToIso (qequal n)) O OD P m).hom ≫
        (R.evaluation m).hom.app (O.extension.obj P) ≫
        (O.extensionEvaluation (t.index m)).hom.app P)
      ((OD.extensionEvaluation m).hom.app (Q.obj P)) := by
  unfold blockOpenExtensionComponent
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.app_inv, Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  exact mappedEquality_heq
    (@SheafOfModules.localizedSystemExtension.{c, v, r} C _ J
      (abelianSheafify.{c, v, max c v r} J)
      (locallyBijective.{c, v, max c v r} J) (B₀ (t.index m)) U)
    (qequal m) P ((OD.extensionEvaluation m).hom.app (Q.obj P))

attribute [local irreducible] evaluation systemRing ringPresheaf rings in
/-- Compatible explicit components assemble naturally and uniquely, with their full
heterogeneous evaluation normalization. Source: Zheng Construction 4.1; Stacks 03DI--03DJ.
(blueprint: lem-pur-block-open-extension-assembly) -/
theorem blockOpenExtensionComparison
    (R : SystemBlockRepetition J B₀ τ₀ t)
    (Q : Systems (J.over U) (openRings.{c, v, r} J B₀ U)
        (openTransitions.{c, v, r} J B₀ τ₀ U) ⥤
      Systems (J.over U) (openRings.{c, v, r} J (blockCoefficients B₀ t) U)
        (openTransitions.{c, v, r} J (blockCoefficients B₀ t)
          (blockTransitions J B₀ τ₀ t) U))
    (qequal : ∀ m : ℕ,
      Q ⋙ evaluation (J.over U) (openRings.{c, v, r} J (blockCoefficients B₀ t) U)
          (openTransitions.{c, v, r} J (blockCoefficients B₀ t)
            (blockTransitions J B₀ τ₀ t) U) m =
        evaluation (J.over U) (openRings.{c, v, r} J B₀ U)
          (openTransitions.{c, v, r} J B₀ τ₀ U) (t.index m))
    (hQ : ∀ (M : Systems (J.over U) (openRings.{c, v, r} J B₀ U)
        (openTransitions.{c, v, r} J B₀ τ₀ U))
      {V W : (ℕ × Over U)ᵒᵖ} (f : V ⟶ W),
      HEq (fun x ↦ (Q.obj M).val.map f x)
        (fun x ↦ M.val.map ((blockSite (C := Over U) t.index).map f.unop).op x)) :
    ∃ (O : OpenSystems.{c, v, r} J B₀ τ₀ U)
      (OD : OpenSystems.{c, v, r} J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t) U),
    (∀ (n : ℕ) N V x, HEq (((O.restrictionEvaluation n).hom.app N).val.app V x) x) ∧
    (∀ (n : ℕ) N V x, HEq (((OD.restrictionEvaluation n).hom.app N).val.app V x) x) ∧
    ∃! ξ : Q ⋙ OD.extension ≅ O.extension ⋙ R.repetition,
      ∀ (m : ℕ)
        (P : Systems (J.over U) (openRings.{c, v, r} J B₀ U)
          (openTransitions.{c, v, r} J B₀ τ₀ U)),
        HEq ((evaluation J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t) m).map
            (ξ.hom.app P) ≫ (R.evaluation m).hom.app (O.extension.obj P) ≫
            (O.extensionEvaluation (t.index m)).hom.app P)
          ((OD.extensionEvaluation m).hom.app
            (Q.obj P)) := by
  classical
  obtain ⟨O, hO⟩ := normalizedOpenSystems.{c, v, r} J B₀ τ₀ U
  obtain ⟨OD, hOD⟩ := normalizedOpenSystems.{c, v, r} J (blockCoefficients B₀ t)
    (blockTransitions J B₀ τ₀ t) U
  let qev (m : ℕ) := eqToIso (qequal m)
  have hqev (m : ℕ) M V x : HEq (((qev m).hom.app M).val.app V x) x :=
    eqToIsoSections (qequal m) M V x
  let d := blockOpenExtensionComponent.{c, v, r} J B₀ τ₀ t U R Q qev O OD
  have ht (P) {m n : ℕ} (h : n ≤ m) :=
    blockOpenExtensionComponent_transition.{c, v, r} J B₀ τ₀ t U R Q qev O OD
      hQ hqev hO hOD P h
  let δ := blockOpenExtensionEvaluationIso.{c, v, r} J B₀ τ₀ t U R Q qev O OD
  have hδ (P) (m : ℕ) : (δ m).hom.app P = (d P m).hom :=
    blockOpenExtensionEvaluationIso_hom.{c, v, r} J B₀ τ₀ t U R Q qev O OD m P
  obtain ⟨ξ, he⟩ := systemNatIsoOfEvaluation.{c, v, r} J (blockCoefficients B₀ t)
    (blockTransitions J B₀ τ₀ t) (Q ⋙ OD.extension) (O.extension ⋙ R.repetition) δ
    (by intro P m n h; simpa only [hδ, d, Functor.comp_obj] using ht P h)
  have hξ (m : ℕ) (P) :
      HEq ((evaluation J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t) m).map
          (ξ.hom.app P) ≫ (R.evaluation m).hom.app (O.extension.obj P) ≫
          (O.extensionEvaluation (t.index m)).hom.app P)
        ((OD.extensionEvaluation m).hom.app (Q.obj P)) := by
    rw [he, hδ]
    exact component_normalization.{c, v, r} J B₀ τ₀ t U R Q qequal O OD m P
  refine ⟨O, OD, hO, hOD, ξ, hξ, ?_⟩
  intro ξ' hξ'
  apply Iso.ext
  apply NatTrans.ext
  funext P
  apply systemHom_ext.{c, v, r} J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t)
  intro m
  have h := eq_of_heq ((hξ' m P).trans (hξ m P).symm)
  exact (cancel_mono ((R.evaluation m).hom.app (O.extension.obj P) ≫
    (O.extensionEvaluation (t.index m)).hom.app P)).mp h

end WeilConjectures.SemilinearSections
