import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationGluing

/-! # Intrinsic generation of actual projective evaluation sections -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.LinearSystem

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

namespace LocalFrame

variable {S : Scheme.{u}} {M : S.Modules} {n : ℕ} {U W : S.Opens}

/-- Every actual local section is the linear combination of its frame coordinates. -/
lemma sum_coordinates_basisSection (e : LocalFrame M n U) (h : W ≤ U) (σ : Γ(M, W)) :
    ∑ i, e.coordinates W h σ i • e.basisSection W h i = σ := by
  simp_rw [basisSection_eq]
  exact (e.coordinates W h).symm_apply_apply σ

end LocalFrame

variable {X S : Scheme.{u}} (p : X ⟶ S) {M : S.Modules} (L : LineBundle X)
    (ev : M ⟶ (Scheme.Modules.pushforward p).obj L.obj)

/-- Evaluate any actual local module section, then convert it on the inverse-image open. -/
def localSectionEvaluation (U : S.Opens) (σ : Γ(M, U)) :
    GlobalSections (evaluationLineBundle p L U).obj :=
  openSection L.obj (p ⁻¹ᵁ U) (ev.app U σ)

/-- Nonvanishing of an actual local section is preserved and detected by open restriction. -/
lemma openSection_nonvan_restrict_iff {A B : X.Opens} (h : A ≤ B)
    (σ : Γ(L.obj, B)) (x : A.toScheme) :
    x ∈ nonvanishingLocus ((LineBundle.pullback A.ι).obj L).obj
        (openSection L.obj A (L.obj.presheaf.map (homOfLE h).op σ)) ↔
      X.homOfLE h x ∈ nonvanishingLocus ((LineBundle.pullback B.ι).obj L).obj
        (openSection L.obj B σ) := by
  rw [← openPullbackIso_hom_openSection L.obj h σ]
  rw [lineBundleResidueOpenComparison]
  change x ∈ trivializationOpen ((Scheme.Modules.pullback A.ι).obj L.obj)
    ((openPullbackIso L.obj h).hom.app ⊤
      (pullbackSection (X.homOfLE h) ((Scheme.Modules.pullback B.ι).obj L.obj)
        (openSection L.obj B σ))) ↔ _
  rw [trivializationOpen_mapIso]
  have hp := lineBundlePullbackSectionOpen B.toScheme A.toScheme (X.homOfLE h)
    ((LineBundle.pullback B.ι).obj L) (openSection L.obj B σ)
  rw [lineBundleResidueOpenComparison]
  exact Iff.of_eq (congrArg (fun O : A.toScheme.Opens => x ∈ O) hp)

/-- Evaluation of a section in frame coordinates is the actual finite linear combination. -/
lemma localSectionEvaluation_eq_sum {n : ℕ} {U W : S.Opens}
    (e : LocalFrame M n U) (h : W ≤ U) (σ : Γ(M, W)) :
    localSectionEvaluation p L ev W σ =
      ∑ i, (p ⁻¹ᵁ W).topIso.inv (p.app W (e.coordinates W h σ i)) •
        localEvaluationSections p L ev e W h i := by
  dsimp only [localSectionEvaluation]
  conv_lhs => rw [← e.sum_coordinates_basisSection h σ]
  rw [map_sum, map_sum]
  simp only [Scheme.Modules.Hom.app_smul]
  change (∑ i, openSection L.obj (p ⁻¹ᵁ W)
      (p.app W (e.coordinates W h σ i) • evaluationSections p ev e W h i)) = _
  simp only [openSection_smul, localEvaluationSections, evaluationSections,
    LocalFrame.evaluatedSections]

/-- One nonvanishing evaluated section forces a nonvanishing evaluated frame basis member. -/
lemma localEvaluationSections_generate_of_section {n : ℕ} {U W : S.Opens}
    (e : LocalFrame M n U) (h : W ≤ U) (σ : Γ(M, W)) (x : (p ⁻¹ᵁ W).toScheme)
    (hσ : x ∈ nonvanishingLocus (evaluationLineBundle p L W).obj
      (localSectionEvaluation p L ev W σ)) :
    ∃ i, x ∈ nonvanishingLocus (evaluationLineBundle p L W).obj
      (localEvaluationSections p L ev e W h i) := by
  classical
  by_contra hx
  simp only [mem_nonvanishingLocus, not_exists, not_not] at hx
  apply (mem_nonvanishingLocus _ _ x).mp hσ
  rw [localSectionEvaluation_eq_sum p L ev e h σ]
  change pullbackSection ((p ⁻¹ᵁ W).toScheme.fromSpecResidueField x)
    (evaluationLineBundle p L W).obj (∑ i, _ • localEvaluationSections p L ev e W h i) = 0
  rw [pullbackSection_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [pullbackSection_smul]
  change _ • residueSection (evaluationLineBundle p L W).obj
    (localEvaluationSections p L ev e W h i) x = 0
  rw [hx i, smul_zero]

/-- Evaluation is intrinsically generated if a local evaluated section is nonzero at each point. -/
def EvaluationGenerates : Prop :=
  ∀ x : X, ∃ (U : S.Opens) (hx : p x ∈ U) (σ : Γ(M, U)),
    (⟨x, hx⟩ : (p ⁻¹ᵁ U).toScheme) ∈
      nonvanishingLocus (evaluationLineBundle p L U).obj
        (localSectionEvaluation p L ev U σ)

/-- Evaluation commutes with actual restriction on the base. -/
lemma localSectionEvaluation_restrict {U W : S.Opens} (h : W ≤ U) (σ : Γ(M, U)) :
    openSection L.obj (p ⁻¹ᵁ W)
        (L.obj.presheaf.map (homOfLE (p.preimage_mono h)).op (ev.app U σ)) =
      localSectionEvaluation p L ev W (M.presheaf.map (homOfLE h).op σ) := by
  apply congrArg (openSection L.obj (p ⁻¹ᵁ W))
  exact (PresheafOfModules.naturality_apply ev.val (homOfLE h).op σ).symm

/-- Intrinsic nonvanishing supplies pointwise generation in every actual local frame. -/
lemma EvaluationGenerates.localFrame {n : ℕ} (hs : EvaluationGenerates p L ev)
    {U : S.Opens} (e : LocalFrame M n U) (W : S.Opens) (hWU : W ≤ U) :
    ∀ x : (p ⁻¹ᵁ W).toScheme, ∃ i,
      x ∈ nonvanishingLocus (evaluationLineBundle p L W).obj
        (localEvaluationSections p L ev e W hWU i) := by
  intro x
  obtain ⟨V, hxV, σ, hσ⟩ := hs x.val
  let T : S.Opens := W ⊓ V
  have hTW : T ≤ W := inf_le_left
  have hTV : T ≤ V := inf_le_right
  let y : (p ⁻¹ᵁ T).toScheme := ⟨x.val, ⟨x.property, hxV⟩⟩
  have hσT : y ∈ nonvanishingLocus (evaluationLineBundle p L T).obj
      (localSectionEvaluation p L ev T (M.presheaf.map (homOfLE hTV).op σ)) := by
    rw [← localSectionEvaluation_restrict p L ev hTV σ]
    apply (openSection_nonvan_restrict_iff L (p.preimage_mono hTV) (ev.app V σ) y).mpr
    have hyV : X.homOfLE (p.preimage_mono hTV) y = ⟨x.val, hxV⟩ :=
      Subtype.ext (Scheme.homOfLE_apply _ y)
    rw [hyV]
    exact hσ
  obtain ⟨i, hi⟩ := localEvaluationSections_generate_of_section p L ev e
    (hTW.trans hWU) (M.presheaf.map (homOfLE hTV).op σ) y hσT
  refine ⟨i, ?_⟩
  have hr := (openSection_nonvan_restrict_iff L (p.preimage_mono hTW)
    (evaluationSections p ev e W hWU i) y).mp
  have he := congrArg (openSection L.obj (p ⁻¹ᵁ T))
    (e.evaluatedSections_restrict ev hTW hWU i)
  have hv := hr (he.symm ▸ hi)
  have hyW : X.homOfLE (p.preimage_mono hTW) y = x :=
    Subtype.ext (Scheme.homOfLE_apply _ y)
  rw [hyW] at hv
  exact hv

/-- Intrinsic generation implies the chosen-frame hypothesis of global gluing. -/
lemma EvaluationGenerates.frameEvaluationGenerates {n : ℕ}
    (hs : EvaluationGenerates p L ev) : FrameEvaluationGenerates p L ev n := by
  intro U
  exact hs.localFrame p L ev (frame M n U) U.val le_rfl

/-- A locally free frame through the image point supplies an intrinsic local witness. -/
lemma FrameEvaluationGenerates.evaluationGenerates {n : ℕ}
    (hM : IsLocallyFreeOfRank M (n + 1)) (hs : FrameEvaluationGenerates p L ev n) :
    EvaluationGenerates p L ev := by
  intro x
  obtain ⟨U, hxU⟩ := exists_frameOpen M n hM (p x)
  obtain ⟨i, hi⟩ := hs U ⟨x, hxU⟩
  exact ⟨U.val, hxU, (frame M n U).basisSection U.val le_rfl i, hi⟩

/-- For a locally free module, intrinsic generation is precisely frame generation. -/
lemma evaluationGenerates_iff_frameEvaluationGenerates {n : ℕ}
    (hM : IsLocallyFreeOfRank M (n + 1)) :
    EvaluationGenerates p L ev ↔ FrameEvaluationGenerates p L ev n :=
  ⟨fun hs => hs.frameEvaluationGenerates p L ev,
    fun hs => hs.evaluationGenerates p L ev hM⟩

end Langlands.AlgebraicGeometry.ProjectiveBundle
