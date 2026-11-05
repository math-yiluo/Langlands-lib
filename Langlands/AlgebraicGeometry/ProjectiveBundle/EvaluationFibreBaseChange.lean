import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationFibreCoordinates

/-! # Actual evaluation sections through canonical direct-image base change -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.LinearSystem
open Langlands.AlgebraicGeometry.Modules.DerivedSections

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

private lemma pullback_map_sectionPullbackLE' {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    {N P : Z.Modules} (a : N ⟶ P) {A : Y.Opens} {B : Z.Opens}
    (h : A ≤ f ⁻¹ᵁ B) (σ : Γ(N, B)) :
    ((Scheme.Modules.pullback f).map a).app A (sectionPullbackLE f N h σ) =
      sectionPullbackLE f P h (a.app B σ) := by
  dsimp only [sectionPullbackLE]
  exact (PresheafOfModules.naturality_apply ((Scheme.Modules.pullback f).map a).val
    (homOfLE h).op _).trans
      (congrArg _ (sectionPullback_naturality f a B σ).symm)

section Square

variable {X S X' S' : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X)
    {M : S.Modules} (ev : M ⟶ (Scheme.Modules.pushforward p).obj L.obj)
    (g : S' ⟶ S) (p' : X' ⟶ S') (q : X' ⟶ X) (w : q ≫ p = p' ≫ g)

include w in
/-- A local base section pulls back over the corresponding changed source open. -/
lemma baseChangeEvaluation_source_mem (U : S.Opens) {V : S'.Opens}
    (hU : V ≤ g ⁻¹ᵁ U) :
    p' ⁻¹ᵁ V ≤ q ⁻¹ᵁ (p ⁻¹ᵁ U) := by
  intro x hx
  change p (q x) ∈ U
  rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
  exact hU hx

/-- The canonical direct-image base-change comparison sends a pulled-back
local coefficient section to the actual pullback of its evaluation. -/
lemma baseChangeEvaluation_sectionPullbackLE (U : S.Opens) {V : S'.Opens}
    (hU : V ≤ g ⁻¹ᵁ U) (σ : Γ(M, U)) :
    (baseChangeEvaluation p L ev g p' q w).app V
        (sectionPullbackLE g M hU σ) =
      sectionPullbackLE q L.obj (baseChangeEvaluation_source_mem p g p' q w U hU)
        (ev.app U σ) := by
  have hq := baseChangeEvaluation_source_mem p g p' q w U hU
  have hr : p' ⁻¹ᵁ V ≤ (p' ≫ g) ⁻¹ᵁ U := fun _ hx => hU hx
  have hs : p' ⁻¹ᵁ V ≤ (q ≫ p) ⁻¹ᵁ U := fun _ hx => hq hx
  have H := congrArg
    (fun a => a.app (p' ⁻¹ᵁ V)
      (sectionPullbackLE p' ((Scheme.Modules.pullback g).obj M)
        le_rfl (sectionPullbackLE g M hU σ)))
    (baseChangeEvaluation_adjunct p L ev g p' q w)
  dsimp only [pullbackSquareIso, Iso.trans_inv, Iso.app_inv, Iso.symm_inv] at H
  simp only [NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply] at H
  erw [pullbackComp_hom_sectionPullbackLE p' g M hU le_rfl hr σ] at H
  erw [pullbackCongr_inv_sectionPullbackLE w M hs hr σ] at H
  erw [pullbackComp_inv_sectionPullbackLE q p M le_rfl hq hs σ] at H
  erw [pullback_map_sectionPullbackLE' q (evaluationAdjoint p L ev) hq] at H
  rw [sectionPullbackLE_self p M U σ,
    evaluationAdjoint_sectionPullback p L ev U σ, sectionPullbackLE_self] at H
  exact (evaluationAdjoint_sectionPullback p'
    ((LineBundle.pullback q).obj L) (baseChangeEvaluation p L ev g p' q w)
    V (sectionPullbackLE g M hU σ)).symm.trans H

end Square

private lemma openLiftPullbackIso_hom_section {X Y : Scheme.{u}}
    (N : X.Modules) (A : X.Opens) (r : Y ⟶ A.toScheme) (q : Y ⟶ X)
    (w : r ≫ A.ι = q) (hq : (⊤ : Y.Opens) ≤ q ⁻¹ᵁ A) (σ : Γ(N, A)) :
    (((Scheme.Modules.pullbackComp r A.ι).app N ≪≫
        (Scheme.Modules.pullbackCongr w).app N).hom.app ⊤)
      (pullbackSection r ((Scheme.Modules.pullback A.ι).obj N) (openSection N A σ)) =
      sectionPullbackLE q N hq σ := by
  have hc : (⊤ : Y.Opens) ≤ (r ≫ A.ι) ⁻¹ᵁ A := by
    rw [w]
    exact hq
  rw [pullbackSection_eq_sectionPullbackLE, openSection_eq_sectionPullbackLE]
  simp only [Iso.trans_hom, Iso.app_hom, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  exact (congrArg (((Scheme.Modules.pullbackCongr w).hom.app N).app ⊤)
    (pullbackComp_hom_sectionPullbackLE r A.ι N
      (show ⊤ ≤ A.ι ⁻¹ᵁ A by simp) (show ⊤ ≤ r ⁻¹ᵁ ⊤ by simp) hc σ)).trans
    (pullbackCongr_hom_sectionPullbackLE w N hc hq σ)

section Fibre

variable {X S : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X)
    {M : S.Modules} (ev : M ⟶ (Scheme.Modules.pushforward p).obj L.obj) {n : ℕ}

/-- The original residue point lies everywhere in a frame open containing its image. -/
lemma fibreFrame_mem (U : FrameOpen M n) (s : S) (hs : s ∈ U.val) :
    (⊤ : (Spec (S.residueField s)).Opens) ≤
      (S.fromSpecResidueField s) ⁻¹ᵁ U.val := by
  intro z _
  change S.fromSpecResidueField s z ∈ U.val
  rw [Scheme.fromSpecResidueField_apply]
  exact hs

/-- Actual frame coefficients pulled back to the original residue spectrum. -/
def fibreFrameSections (U : FrameOpen M n) (s : S) (hs : s ∈ U.val) :
    Fin (n + 1) → GlobalSections
      ((Scheme.Modules.pullback (S.fromSpecResidueField s)).obj M) :=
  fun i => sectionPullbackLE (S.fromSpecResidueField s) M (fibreFrame_mem U s hs)
    ((frame M n U).basisSection U.val le_rfl i)

/-- The canonical comparison from the two-step restriction to the actual fibre bundle. -/
def fibreEvaluationLineIso (U : FrameOpen M n) (s : S) (hs : s ∈ U.val) :
    ((LineBundle.pullback (fibreSourceLift p U s hs)).obj
      (evaluationLineBundle p L U.val)).obj ≅
        ((LineBundle.pullback (p.fiberι s)).obj L).obj :=
  (Scheme.Modules.pullbackComp (fibreSourceLift p U s hs) (p ⁻¹ᵁ U.val).ι).app L.obj ≪≫
    (Scheme.Modules.pullbackCongr (fibreSourceLift_ι p U s hs)).app L.obj

/-- The sections obtained from the actual canonical base-change evaluation. -/
def fibreFrameEvaluation (U : FrameOpen M n) (s : S) (hs : s ∈ U.val) :
    Fin (n + 1) → GlobalSections ((LineBundle.pullback (p.fiberι s)).obj L).obj :=
  fun i => (baseChangeEvaluation p L ev (S.fromSpecResidueField s)
    (p.fiberToSpecResidueField s) (p.fiberι s) (p.fiber_fac s)).app ⊤
      (fibreFrameSections U s hs i)

/-- The two-step restriction carries precisely the canonical changed evaluation sections. -/
lemma fibreEvaluationLineIso_hom_sections (U : FrameOpen M n) (s : S)
    (hs : s ∈ U.val) (i : Fin (n + 1)) :
    (fibreEvaluationLineIso p L U s hs).hom.app ⊤
        (fibreEvaluationSections p L ev U s hs i) =
      fibreFrameEvaluation p L ev U s hs i := by
  have hq : (⊤ : (p.fiber s).Opens) ≤ (p.fiberι s) ⁻¹ᵁ (p ⁻¹ᵁ U.val) := by
    exact baseChangeEvaluation_source_mem p (S.fromSpecResidueField s)
      (p.fiberToSpecResidueField s) (p.fiberι s) (p.fiber_fac s) U.val
      (fibreFrame_mem U s hs)
  have he :
      (fibreEvaluationLineIso p L U s hs).hom.app ⊤
          (fibreEvaluationSections p L ev U s hs i) =
        sectionPullbackLE (p.fiberι s) L.obj hq
          (ev.app U.val ((frame M n U).basisSection U.val le_rfl i)) := by
    exact openLiftPullbackIso_hom_section L.obj (p ⁻¹ᵁ U.val)
      (fibreSourceLift p U s hs) (p.fiberι s) (fibreSourceLift_ι p U s hs) hq
      (evaluationSections p ev (frame M n U) U.val le_rfl i)
  exact he.trans (baseChangeEvaluation_sectionPullbackLE p L ev
    (S.fromSpecResidueField s) (p.fiberToSpecResidueField s) (p.fiberι s)
    (p.fiber_fac s) U.val (fibreFrame_mem U s hs)
    ((frame M n U).basisSection U.val le_rfl i)).symm

variable (hgen : FrameEvaluationGenerates p L ev n)

include hgen in
/-- The canonical changed evaluation sections generate whenever the original frame does. -/
lemma fibreFrameEvaluation_generate (U : FrameOpen M n) (s : S)
    (hs : s ∈ U.val) :
    ∀ x : p.fiber s, ∃ i, x ∈ nonvanishingLocus
      ((LineBundle.pullback (p.fiberι s)).obj L).obj
      (fibreFrameEvaluation p L ev U s hs i) := by
  have ht := mapIsoSections_generate
    (L := (LineBundle.pullback (fibreSourceLift p U s hs)).obj
      (evaluationLineBundle p L U.val))
    (M := (LineBundle.pullback (p.fiberι s)).obj L)
    (fibreEvaluationLineIso p L U s hs)
    (fibreEvaluationSections_generate p L ev hgen U s hs)
  intro x
  obtain ⟨i, hi⟩ := ht x
  refine ⟨i, ?_⟩
  exact (congrArg (fun σ => x ∈ nonvanishingLocus
    ((LineBundle.pullback (p.fiberι s)).obj L).obj σ)
    (fibreEvaluationLineIso_hom_sections p L ev U s hs i)).mp hi

/-- The actual changed evaluation gives the coordinates of the canonical fibre map. -/
lemma fibreFrameEvaluation_coordinates (U : FrameOpen M n) (s : S)
    (hs : s ∈ U.val) :
    relativeLinearSystemMap (p.fiberToSpecResidueField s)
        (fibreFrameEvaluation_generate p L ev hgen U s hs) =
      fibreEvaluationCoordinates p L ev hgen U s hs := by
  have ht := relativeLinearSystemMap_mapIso (p.fiberToSpecResidueField s)
    (L := (LineBundle.pullback (fibreSourceLift p U s hs)).obj
      (evaluationLineBundle p L U.val))
    (M := (LineBundle.pullback (p.fiberι s)).obj L)
    (fibreEvaluationLineIso p L U s hs)
    (fibreEvaluationSections_generate p L ev hgen U s hs)
  have he : mapIsoSections
      (L := (LineBundle.pullback (fibreSourceLift p U s hs)).obj
        (evaluationLineBundle p L U.val))
      (M := (LineBundle.pullback (p.fiberι s)).obj L)
      (fibreEvaluationLineIso p L U s hs)
      (fibreEvaluationSections p L ev U s hs) =
      fibreFrameEvaluation p L ev U s hs := by
    funext i
    exact fibreEvaluationLineIso_hom_sections p L ev U s hs i
  simpa only [he, fibreEvaluationCoordinates] using ht

end Fibre

end Langlands.AlgebraicGeometry.ProjectiveBundle
