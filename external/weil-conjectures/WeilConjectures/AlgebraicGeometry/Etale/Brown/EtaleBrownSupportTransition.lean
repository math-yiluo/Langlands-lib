/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSystemBrownConstruction
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownEvaluationMate
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemUnboundedComparison

/-! # Canonical Brown comparison transition
Source: Zheng, Construction 5.15 and Lemma 5.16, printed pp. 34--35.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open scoped CategoryTheory.TwoSquare
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits SheafOfModules
namespace AlgebraicGeometry
attribute [instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
variable {O : Type (u + 1)} [CommRing O] {t : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  {S : StrictEtaleCompactSupport O t c}
  (B : StrictEtaleBrownConstruction O t c S)

section MateCalculus
universe a av b bv c cv d dv e ev f fv
variable {A : Type a} [Category.{av} A] {B₀ : Type b} [Category.{bv} B₀]
  {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]

private theorem conjugate_transpose
    {L L' : A ⥤ B₀} {R R' : B₀ ⥤ A} (a : L ⊣ R) (b : L' ⊣ R')
    (e : L' ≅ L) (P : A) (Q : B₀) (f : L.obj P ⟶ Q) :
    b.homEquiv P Q (e.hom.app P ≫ f) =
      a.homEquiv P Q f ≫ (conjugateIsoEquiv a b e).hom.app Q := by
  rw [a.homEquiv_unit, b.homEquiv_unit, Category.assoc]
  rw [show R.map f ≫ (conjugateIsoEquiv a b e).hom.app Q =
    (conjugateIsoEquiv a b e).hom.app (L.obj P) ≫ R'.map f from
      (conjugateIsoEquiv a b e).hom.naturality f]
  rw [← Category.assoc]
  erw [unit_conjugateEquiv]
  simp only [Functor.map_comp, Category.assoc]

private theorem conjugate_of_transpose
    {L L' : A ⥤ B₀} {R R' : B₀ ⥤ A} (a : L ⊣ R) (b : L' ⊣ R')
    (e : L' ≅ L) (δ : R ≅ R')
    (h : ∀ P Q (f : L'.obj P ⟶ Q),
      b.homEquiv P Q f = a.homEquiv P Q (e.inv.app P ≫ f) ≫ δ.hom.app Q) :
    conjugateIsoEquiv a b e = δ := by
  apply Iso.ext
  apply NatTrans.ext
  funext Q
  have hh := h (R.obj Q) Q (e.hom.app _ ≫ a.counit.app Q)
  rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at hh
  have hc := conjugate_transpose a b e (R.obj Q) Q (a.counit.app Q)
  have hi : a.homEquiv (R.obj Q) Q (a.counit.app Q) = 𝟙 _ := by
    rw [← a.homEquiv_symm_id Q]
    exact Equiv.apply_symm_apply _ _
  rw [hi, Category.id_comp] at hh hc
  exact hc.symm.trans hh

private theorem scalar_conjugate
    {TA : A ⥤ B₀} {RA : B₀ ⥤ A} (a : TA ⊣ RA)
    {TB : C ⥤ D} {RB : D ⥤ C} (b : TB ⊣ RB)
    {Fm : A ⥤ C} {Gm : C ⥤ A} (am : Fm ⊣ Gm)
    {Fn : B₀ ⥤ D} {Gn : D ⥤ B₀} (an : Fn ⊣ Gn)
    (γ : TA ⋙ Fn ≅ Fm ⋙ TB) (δ : RB ⋙ Gm ≅ Gn ⋙ RA)
    (h : ∀ P Q (f : Fn.obj (TA.obj P) ⟶ Q),
      a.homEquiv P _ (an.homEquiv _ Q f) =
        am.homEquiv P _ (b.homEquiv _ Q (γ.inv.app P ≫ f)) ≫ δ.hom.app Q) :
    conjugateIsoEquiv (am.comp b) (a.comp an) γ = δ := by
  apply conjugate_of_transpose
  intro P Q f
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change a.homEquiv P _ (an.homEquiv _ Q f) =
    am.homEquiv P _ (b.homEquiv _ Q (γ.inv.app P ≫ f)) ≫ δ.hom.app Q
  exact h P Q f

private theorem mate_of_unit
    {L : A ⥤ B₀} {R : B₀ ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') {F : A ⥤ C} {G : B₀ ⥤ D}
    (α : F ⋙ L' ⟶ L ⋙ G) (β : R ⋙ F ⟶ G ⋙ R')
    (h : ∀ P, b.homEquiv _ _ (α.app P) =
      F.map (a.unit.app P) ≫ β.app (L.obj P)) :
    (mateEquiv a b (.mk _ _ _ _ α)) = β := by
  apply (mateEquiv a b).symm.injective
  rw [Equiv.symm_apply_apply]
  apply NatTrans.ext
  funext P
  apply (b.homEquiv _ _).injective
  change b.homEquiv _ _ (α.app P) = b.homEquiv _ _
    ((((mateEquiv a b).symm (.mk _ _ _ _ β))).app P)
  exact (h P).trans (unit_mateEquiv_symm a b (.mk _ _ _ _ β) P)

private def transposeTransition
    {L : A ⥤ B₀} {R : B₀ ⥤ A} (a : L ⊣ R) {E : Type e} [Category.{ev} E]
    {F : E ⥤ A} {G : E ⥤ B₀} (τ : F ⟶ G ⋙ R) : F ⋙ L ⟶ G where
  app P := (a.homEquiv _ _).symm (τ.app P)
  naturality {P Q} f := by
    apply (a.homEquiv _ _).injective
    rw [Functor.comp_map, a.homEquiv_naturality_left, a.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact τ.naturality f

private theorem tensor_transition
    {TA : A ⥤ B₀} {RA : B₀ ⥤ A} (a : TA ⊣ RA)
    {TB : C ⥤ D} {RB : D ⥤ C} (b : TB ⊣ RB)
    {Fm : A ⥤ C} {Fn : B₀ ⥤ D}
    (γ : TA ⋙ Fn ≅ Fm ⋙ TB) (δ : RA ⋙ Fm ≅ Fn ⋙ RB)
    (hmate : (mateEquiv a b (.mk _ _ _ _ γ.inv)) = δ.hom)
    {Nm : C} {Nn : D} {Mm : A} {Mn : B₀}
    (em : Nm ≅ Fm.obj Mm) (en : Nn ≅ Fn.obj Mn)
    (τM : Mm ⟶ RA.obj Mn) (τN : Nm ⟶ RB.obj Nn)
    (hτ : τN ≫ RB.map en.hom = em.hom ≫ Fm.map τM ≫ δ.hom.app Mn) :
    Fn.map ((a.homEquiv _ _).symm τM) ≫ en.inv =
      γ.hom.app Mm ≫ TB.map em.inv ≫ (b.homEquiv _ _).symm τN := by
  apply (cancel_epi (γ.inv.app Mm)).1
  apply (cancel_mono en.hom).1
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id,
    Category.comp_id]
  apply (b.homEquiv _ _).injective
  have hm := adjunctionMate_transpose a b (.mk _ _ _ _ δ.hom) Mm Mn
    ((a.homEquiv _ _).symm τM)
  have he : (mateEquiv a b).symm (.mk _ _ _ _ δ.hom) =
      .mk _ _ _ _ γ.inv := by
    rw [← hmate]
    exact Equiv.symm_apply_apply _ _
  rw [he, Equiv.apply_symm_apply] at hm
  rw [hm, b.homEquiv_naturality_left]
  rw [b.homEquiv_naturality_right, Equiv.apply_symm_apply]
  rw [hτ, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

variable {E : Type e} [Category.{ev} E] {F₀ : Type f} [Category.{fv} F₀]

private theorem left_tensor_transition
    {Fs : E ⥤ F₀} {Gs : F₀ ⥤ E} (asys : Fs ⊣ Gs)
    {Fm : A ⥤ C} {Gm : C ⥤ A} (am : Fm ⊣ Gm)
    {Fn : B₀ ⥤ D} {Gn : D ⥤ B₀} (an : Fn ⊣ Gn)
    {TA : A ⥤ B₀} {TB : C ⥤ D}
    {EAm : E ⥤ A} {EAn : E ⥤ B₀} {EBm : F₀ ⥤ C} {EBn : F₀ ⥤ D}
    (em : Fs ⋙ EBm ≅ EAm ⋙ Fm) (en : Fs ⋙ EBn ≅ EAn ⋙ Fn)
    (γ : TA ⋙ Fn ≅ Fm ⋙ TB)
    (tA : EAm ⋙ TA ⟶ EAn) (tB : EBm ⋙ TB ⟶ EBn)
    (ht : ∀ M,
      TA.map ((mateEquiv asys am (.mk _ _ _ _ em.inv)).app M) ≫
        (mateEquiv am an (.mk _ _ _ _ γ.hom)).app (EBm.obj M) ≫
        Gn.map (tB.app M) =
      tA.app (Gs.obj M) ≫ (mateEquiv asys an (.mk _ _ _ _ en.inv)).app M)
    (K : E) :
    Fn.map (tA.app K) ≫ en.inv.app K =
      γ.hom.app (EAm.obj K) ≫ TB.map (em.inv.app K) ≫ tB.app (Fs.obj K) := by
  let τm : TwoSquare EAm Fs Fm EBm := em.inv
  let τn : TwoSquare EAn Fs Fn EBn := en.inv
  let π : TwoSquare TA Fm Fn TB := γ.hom
  have hh : (τm.hComp π).whiskerBottom tB = τn.whiskerTop tA := by
    apply (mateEquiv asys an).injective
    rw [SheafOfModules.mate_whiskerBottom asys an,
      SheafOfModules.mate_whiskerTop asys an, mateEquiv_vcomp asys am an]
    apply NatTrans.ext
    funext M
    simpa only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
      TwoSquare.vComp_app, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc, τm, τn, π] using ht M
  have hc := congr_app hh K
  simpa only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc, τm, τn, π] using hc.symm

private theorem left_tensor_transition_of_right
    {Fs : E ⥤ F₀} {Gs : F₀ ⥤ E} (asys : Fs ⊣ Gs)
    {Fm : A ⥤ C} {Gm : C ⥤ A} (am : Fm ⊣ Gm)
    {Fn : B₀ ⥤ D} {Gn : D ⥤ B₀} (an : Fn ⊣ Gn)
    {TA : A ⥤ B₀} {TB : C ⥤ D}
    {EAm : E ⥤ A} {EAn : E ⥤ B₀} {EBm : F₀ ⥤ C} {EBn : F₀ ⥤ D}
    (em : Fs ⋙ EBm ≅ EAm ⋙ Fm) (en : Fs ⋙ EBn ≅ EAn ⋙ Fn)
    (γ : TA ⋙ Fn ≅ Fm ⋙ TB)
    (rm : Gs ⋙ EAm ≅ EBm ⋙ Gm) (rn : Gs ⋙ EAn ≅ EBn ⋙ Gn)
    (δ : TB ⋙ Gn ≅ Gm ⋙ TA)
    (hm : (mateEquiv asys am (.mk _ _ _ _ em.inv)) = rm.hom)
    (hn : (mateEquiv asys an (.mk _ _ _ _ en.inv)) = rn.hom)
    (hγ : (mateEquiv am an (.mk _ _ _ _ γ.hom)) = δ.inv)
    (tA : EAm ⋙ TA ⟶ EAn) (tB : EBm ⋙ TB ⟶ EBn)
    (ht : ∀ H, Gn.map (tB.app H) ≫ rn.inv.app H =
      δ.hom.app (EBm.obj H) ≫ TA.map (rm.inv.app H) ≫ tA.app (Gs.obj H))
    (K : E) :
    Fn.map (tA.app K) ≫ en.inv.app K =
      γ.hom.app (EAm.obj K) ≫ TB.map (em.inv.app K) ≫ tB.app (Fs.obj K) := by
  apply left_tensor_transition asys am an em en γ tA tB ?_ K
  intro H
  rw [hm, hn, hγ]
  apply (cancel_epi (TA.map (rm.inv.app H))).1
  rw [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  erw [Category.id_comp]
  apply (cancel_epi (δ.hom.app (EBm.obj H))).1
  rw [← Category.assoc, Iso.hom_inv_id_app]
  erw [Category.id_comp]
  apply (cancel_mono (rn.inv.app H)).1
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  exact ht H

private theorem scalar_inverse_mate
    {TA : A ⥤ B₀} {RA : B₀ ⥤ A} (a : TA ⊣ RA)
    {TB : C ⥤ D} {RB : D ⥤ C} (b : TB ⊣ RB)
    {Fm : A ⥤ C} {Gm : C ⥤ A} (am : Fm ⊣ Gm)
    {Fn : B₀ ⥤ D} {Gn : D ⥤ B₀} (an : Fn ⊣ Gn)
    (γ : TA ⋙ Fn ≅ Fm ⋙ TB) (δ : RB ⋙ Gm ≅ Gn ⋙ RA)
    (β : RA ⋙ Fm ≅ Fn ⋙ RB)
    (hc : conjugateIsoEquiv (am.comp b) (a.comp an) γ = δ)
    (hβ : ∀ P, am.homEquiv _ _ (β.hom.app P) =
      RA.map (an.unit.app P) ≫ δ.inv.app (Fn.obj P)) :
    (mateEquiv a b (.mk _ _ _ _ γ.inv)) = β.hom := by
  apply (mateEquiv an am).injective
  have hh := iterated_mateEquiv_conjugateEquiv a b am an
    (.mk _ _ _ _ γ.inv)
  have hi : conjugateEquiv (a.comp an) (am.comp b) γ.inv = δ.inv := by
    exact congrArg Iso.inv hc
  rw [hi] at hh
  exact hh.trans (mate_of_unit an am β.hom δ.inv hβ).symm

end MateCalculus

private theorem proper_scalar_mate {m n : ℕ} (h : n ≤ m) :
    (mateEquiv (S.PZ.scalar h).derivedAdj (S.PY.scalar h).derivedAdj
      (.mk _ _ _ _ (B.properProjection h).inv)) =
    (S.properDerived.restrictedDirect h).hom := by
  rw [B.properMate]
  rw [iterated_mateEquiv_conjugateEquiv
    (S.properDerived.level m).adjunction (S.properDerived.level n).adjunction
    (S.PY.scalar h).derivedAdj (S.PZ.scalar h).derivedAdj]
  exact congrArg Iso.hom (scalar_conjugate
    (S.PY.scalar h).derivedAdj (S.PZ.scalar h).derivedAdj
    (S.properDerived.level m).adjunction (S.properDerived.level n).adjunction
    (S.properDerived.derivedTensor h) (S.properDerived.restrictedDirect h)
    (S.properDerived.restrictedDirect_mate h))

private theorem inverse_scalar_mate {m n : ℕ} (h : n ≤ m) :
    (mateEquiv (S.PZ.scalar h).derivedAdj (S.PX.scalar h).derivedAdj
      (.mk _ _ _ _ (S.openDerived.derivedTensor h).inv)) =
    (S.openDerived.restrictedInverse h).hom := by
  exact scalar_inverse_mate (S.PZ.scalar h).derivedAdj (S.PX.scalar h).derivedAdj
    (S.openDerived.level m).adjunction (S.openDerived.level n).adjunction
    (S.openDerived.derivedTensor h) (S.openDerived.restrictedDirect h)
    (S.openDerived.restrictedInverse h)
    (scalar_conjugate (S.PZ.scalar h).derivedAdj (S.PX.scalar h).derivedAdj
      (S.openDerived.level m).adjunction (S.openDerived.level n).adjunction
      (S.openDerived.derivedTensor h) (S.openDerived.restrictedDirect h)
      (S.openDerived.restrictedDirect_mate h))
    (S.openDerived.restrictedInverse_mate h)

private theorem inverse_tensor_transition {m n : ℕ} (h : n ≤ m)
    (H : DerivedCategory (strictEtaleCoefficientSystem c.Z O t)) :
    (S.openDerived.level n).inverse.map
        (((S.PZ.scalar h).derivedAdj.homEquiv _ _).symm ((S.PZ.transition h).app H)) ≫
      (S.openDerived.inverseEvaluation n).inv.app H =
    (S.openDerived.derivedTensor h).hom.app ((S.PZ.evaluation m).obj H) ≫
      (S.PX.scalar h).derived.map ((S.openDerived.inverseEvaluation m).inv.app H) ≫
      (((S.PX.scalar h).derivedAdj.homEquiv _ _).symm
        ((S.PX.transition h).app (S.openDerived.system.inverse.obj H))) := by
  exact tensor_transition (S.PZ.scalar h).derivedAdj (S.PX.scalar h).derivedAdj
    (S.openDerived.derivedTensor h) (S.openDerived.restrictedInverse h)
    (inverse_scalar_mate (S := S) h)
    ((S.openDerived.inverseEvaluation m).app H)
    ((S.openDerived.inverseEvaluation n).app H)
    ((S.PZ.transition h).app H)
    ((S.PX.transition h).app (S.openDerived.system.inverse.obj H))
    (S.openDerived.inverseTransition h H)

private theorem proper_tensor_transition {m n : ℕ} (h : n ≤ m)
    (H : DerivedCategory (strictEtaleCoefficientSystem c.Z O t)) :
    (S.properDerived.level n).direct.map
        (((S.PZ.scalar h).derivedAdj.homEquiv _ _).symm ((S.PZ.transition h).app H)) ≫
      (S.properDerived.directEvaluation n).inv.app H =
    (B.properProjection h).hom.app ((S.PZ.evaluation m).obj H) ≫
      (S.PY.scalar h).derived.map ((S.properDerived.directEvaluation m).inv.app H) ≫
      (((S.PY.scalar h).derivedAdj.homEquiv _ _).symm
        ((S.PY.transition h).app (S.properDerived.system.direct.obj H))) := by
  exact tensor_transition (S.PZ.scalar h).derivedAdj (S.PY.scalar h).derivedAdj
    (B.properProjection h) (S.properDerived.restrictedDirect h)
    (proper_scalar_mate B h)
    ((S.properDerived.directEvaluation m).app H)
    ((S.properDerived.directEvaluation n).app H)
    ((S.PZ.transition h).app H)
    ((S.PY.transition h).app (S.properDerived.system.direct.obj H))
    (S.properDerived.directTransition h H)

private theorem open_tensor_transition {m n : ℕ} (h : n ≤ m)
    (K : DerivedCategory (strictEtaleCoefficientSystem X O t)) :
    (S.levelDerivedOpen n).map
        (((S.PX.scalar h).derivedAdj.homEquiv _ _).symm ((S.PX.transition h).app K)) ≫
      (S.openDerivedEvaluation n).inv.app K =
    (B.openProjection h).hom.app ((S.PX.evaluation m).obj K) ≫
      (S.PZ.scalar h).derived.map ((S.openDerivedEvaluation m).inv.app K) ≫
      (((S.PZ.scalar h).derivedAdj.homEquiv _ _).symm
        ((S.PZ.transition h).app (S.derivedOpen.obj K))) := by
  let tX := transposeTransition (S.PX.scalar h).derivedAdj (S.PX.transition h)
  let tZ := transposeTransition (S.PZ.scalar h).derivedAdj (S.PZ.transition h)
  exact left_tensor_transition_of_right S.derivedOpenAdjunction
    (S.levelDerivedOpenAdjunction m) (S.levelDerivedOpenAdjunction n)
    (S.openDerivedEvaluation m) (S.openDerivedEvaluation n) (B.openProjection h)
    (S.openDerived.inverseEvaluation m) (S.openDerived.inverseEvaluation n)
    (S.openDerived.derivedTensor h)
    (etaleBrownEvaluationMate B m).1 (etaleBrownEvaluationMate B n).1 (B.openMate h)
    tX tZ (fun H ↦ inverse_tensor_transition (S := S) h H) K

/-- The canonical compact-support evaluation respects actual derived transitions.
Source: Zheng, Construction 5.15 and Lemma 5.16, printed pp. 34--35
(blueprint: lem-pur-etale-brown-support-transition).

Proof: transpose the strict transition square of the open and proper image
comparisons through their recorded scalar adjunctions. The open and proper mate
identities identify the resulting squares with the inverse-image tensor transition
and direct-image transition. Paste the two squares using projection_def and
naturality of properProjection, then expand S.evaluation and cancel the comparison
isomorphisms. This gives the displayed equation for every unbounded derived input.
The argument uses no flatness or boundedness assumption. -/
theorem etaleBrownSupportTransition {m n : ℕ} (h : n ≤ m)
    (K : DerivedCategory (strictEtaleCoefficientSystem X O t)) :
    (S.levelFunctor n).map
        (((S.PX.scalar h).derivedAdj.homEquiv _ _).symm ((S.PX.transition h).app K)) ≫
      (S.evaluation n).inv.app K =
    (B.projection h).hom.app ((S.PX.evaluation m).obj K) ≫
      (S.PY.scalar h).derived.map ((S.evaluation m).inv.app K) ≫
      (((S.PY.scalar h).derivedAdj.homEquiv _ _).symm
        ((S.PY.transition h).app (S.functor.obj K))) := by
  let τX := ((S.PX.scalar h).derivedAdj.homEquiv _ _).symm
    ((S.PX.transition h).app K)
  let τZ := ((S.PZ.scalar h).derivedAdj.homEquiv _ _).symm
    ((S.PZ.transition h).app (S.derivedOpen.obj K))
  let τY := ((S.PY.scalar h).derivedAdj.homEquiv _ _).symm
    ((S.PY.transition h).app (S.functor.obj K))
  have ho := open_tensor_transition B h K
  have hp := proper_tensor_transition B h (S.derivedOpen.obj K)
  change (S.levelDerivedOpen n).map τX ≫ (S.openDerivedEvaluation n).inv.app K =
    (B.openProjection h).hom.app ((S.PX.evaluation m).obj K) ≫
      (S.PZ.scalar h).derived.map ((S.openDerivedEvaluation m).inv.app K) ≫ τZ at ho
  change (S.properDerived.level n).direct.map τZ ≫
      (S.properDerived.directEvaluation n).inv.app (S.derivedOpen.obj K) =
    (B.properProjection h).hom.app ((S.PZ.evaluation m).obj (S.derivedOpen.obj K)) ≫
      (S.PY.scalar h).derived.map
        ((S.properDerived.directEvaluation m).inv.app (S.derivedOpen.obj K)) ≫ τY at hp
  have hn := (B.properProjection h).hom.naturality
    ((S.openDerivedEvaluation m).inv.app K)
  change (S.properDerived.level n).direct.map
      ((S.PZ.scalar h).derived.map ((S.openDerivedEvaluation m).inv.app K)) ≫
        (B.properProjection h).hom.app ((S.PZ.evaluation m).obj (S.derivedOpen.obj K)) =
      (B.properProjection h).hom.app
          ((S.levelDerivedOpen m).obj ((S.PX.evaluation m).obj K)) ≫
        (S.PY.scalar h).derived.map
          ((S.properDerived.level m).direct.map ((S.openDerivedEvaluation m).inv.app K))
    at hn
  have he : (S.properDerived.level n).direct.map ((S.levelDerivedOpen n).map τX) ≫
      (S.properDerived.level n).direct.map ((S.openDerivedEvaluation n).inv.app K) ≫
      (S.properDerived.directEvaluation n).inv.app (S.derivedOpen.obj K) =
    (S.properDerived.level n).direct.map
        ((B.openProjection h).hom.app ((S.PX.evaluation m).obj K)) ≫
      (B.properProjection h).hom.app
        ((S.levelDerivedOpen m).obj ((S.PX.evaluation m).obj K)) ≫
      (S.PY.scalar h).derived.map
        ((S.properDerived.level m).direct.map ((S.openDerivedEvaluation m).inv.app K) ≫
          (S.properDerived.directEvaluation m).inv.app (S.derivedOpen.obj K)) ≫ τY := by
    rw [← Category.assoc, ← Functor.map_comp, ho]
    simp only [Functor.map_comp, Category.assoc]
    rw [hp, reassoc_of% hn]
  simpa [StrictEtaleCompactSupport.levelFunctor, StrictEtaleCompactSupport.evaluation,
    B.projection_def, Category.assoc, τX, τY] using he

end AlgebraicGeometry
