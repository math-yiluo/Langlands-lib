import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationMorphism
import Langlands.AlgebraicGeometry.Modules.PullbackAffineSections
import Langlands.AlgebraicGeometry.Modules.SectionPullbackBridge
import Langlands.AlgebraicGeometry.LinearSystem.BundleComparison

/-! # Restriction of actual local evaluation morphisms -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.LinearSystem

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

variable {X S : Scheme.{u}}

/-- The open-section conversion is the actual adjunction section pullback. -/
lemma openSection_eq_sectionPullbackLE (N : X.Modules) (A : X.Opens) (s : Γ(N, A)) :
    openSection N A s = sectionPullbackLE A.ι N (show ⊤ ≤ A.ι ⁻¹ᵁ A by simp) s := by
  let θ := (Scheme.Modules.restrictFunctorIsoPullback A.ι).app N
  apply (ConcreteCategory.bijective_of_isIso (θ.inv.app ⊤)).injective
  have hid := congrArg (fun f => f.app ⊤
      ((N.restrictAppIso A.ι ⊤).inv (N.presheaf.map (eqToHom A.ι_image_top).op s)))
    θ.hom_inv_id
  change θ.inv.app ⊤ (openSection N A s) =
      (N.restrictAppIso A.ι ⊤).inv (N.presheaf.map (eqToHom A.ι_image_top).op s) at hid
  rw [hid]
  dsimp only [sectionPullbackLE]
  change (N.restrictAppIso A.ι ⊤).inv (N.presheaf.map (eqToHom A.ι_image_top).op s) =
    θ.inv.val.app (op ⊤) (((Scheme.Modules.pullback A.ι).obj N).val.map
      (homOfLE (show ⊤ ≤ A.ι ⁻¹ᵁ A by simp)).op (sectionPullback A.ι N A s))
  rw [PresheafOfModules.naturality_apply θ.inv.val]
  have hu := Langlands.AlgebraicGeometry.Modules.DerivedSections.pullback_unit_app_comp_restrictFunctorIsoPullback_inv
    A.ι N A
  have hs := ConcreteCategory.congr_hom hu s
  change θ.inv.val.app (op (A.ι ⁻¹ᵁ A)) (sectionPullback A.ι N A s) = _ at hs
  rw [hs]
  change N.presheaf.map (eqToHom A.ι_image_top).op s =
    N.presheaf.map _ (N.presheaf.map _ s)
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Global section pullback is the top-open case of restricted section pullback. -/
lemma pullbackSection_eq_sectionPullbackLE {Y : Scheme.{u}} (f : Y ⟶ X) (N : X.Modules)
    (s : GlobalSections N) :
    pullbackSection f N s =
      sectionPullbackLE f N (show ⊤ ≤ f ⁻¹ᵁ ⊤ by simp) s := by
  rw [pullbackSection_eq_sectionPullback]
  exact (sectionPullbackLE_self f N ⊤ s).symm

/-- The canonical comparison between restriction in two steps and in one step. -/
def openPullbackIso (N : X.Modules) {A B : X.Opens} (h : A ≤ B) :
    (Scheme.Modules.pullback (X.homOfLE h)).obj ((Scheme.Modules.pullback B.ι).obj N) ≅
      (Scheme.Modules.pullback A.ι).obj N :=
  (Scheme.Modules.pullbackComp (X.homOfLE h) B.ι).app N ≪≫
    (Scheme.Modules.pullbackCongr (X.homOfLE_ι h)).app N

/-- This canonical comparison carries the pulled-back section to its actual restriction. -/
lemma openPullbackIso_hom_openSection (N : X.Modules) {A B : X.Opens} (h : A ≤ B)
    (s : Γ(N, B)) :
    (openPullbackIso N h).hom.app ⊤
        (pullbackSection (X.homOfLE h) ((Scheme.Modules.pullback B.ι).obj N)
          (openSection N B s)) =
      openSection N A (N.presheaf.map (homOfLE h).op s) := by
  rw [pullbackSection_eq_sectionPullbackLE, openSection_eq_sectionPullbackLE,
    openSection_eq_sectionPullbackLE]
  simp only [openPullbackIso, Iso.trans_hom, Iso.app_hom,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  erw [pullbackComp_hom_sectionPullbackLE (X.homOfLE h) B.ι N
    (show ⊤ ≤ B.ι ⁻¹ᵁ B by simp) (show ⊤ ≤ (X.homOfLE h) ⁻¹ᵁ ⊤ by simp)
    (show ⊤ ≤ (X.homOfLE h ≫ B.ι) ⁻¹ᵁ B by rw [X.homOfLE_ι h]; exact fun x _ => h x.property)]
  erw [pullbackCongr_hom_sectionPullbackLE (X.homOfLE_ι h) N _
    (show ⊤ ≤ A.ι ⁻¹ᵁ B from fun x _ => h x.property)]
  exact (sectionPullbackLE_restrict A.ι N h (show ⊤ ≤ A.ι ⁻¹ᵁ A by simp) s).symm

variable (p : X ⟶ S) {M : S.Modules} (L : LineBundle X) {n : ℕ}
    (ev : M ⟶ (Scheme.Modules.pushforward p).obj L.obj)

/-- Actual evaluated sections agree across the canonical restriction comparison. -/
lemma localEvaluationSections_restrict {U W T : S.Opens} (e : LocalFrame M n U)
    (hTW : T ≤ W) (hWU : W ≤ U) (i : Fin (n + 1)) :
    (openPullbackIso L.obj (p.preimage_mono hTW)).hom.app ⊤
        (pullbackSection (X.homOfLE (p.preimage_mono hTW))
          (evaluationLineBundle p L W).obj (localEvaluationSections p L ev e W hWU i)) =
      localEvaluationSections p L ev e T (hTW.trans hWU) i := by
  exact (openPullbackIso_hom_openSection L.obj (p.preimage_mono hTW)
    (evaluationSections p ev e W hWU i)).trans
    (congrArg (openSection L.obj (p ⁻¹ᵁ T))
      (e.evaluatedSections_restrict ev hTW hWU i))

/-- Generation on a frame open restricts to every smaller base open. -/
lemma localEvaluationSections_restrict_generate {U W T : S.Opens} (e : LocalFrame M n U)
    (hTW : T ≤ W) (hWU : W ≤ U)
    (hs : ∀ x : (p ⁻¹ᵁ W).toScheme, ∃ i,
      x ∈ nonvanishingLocus (evaluationLineBundle p L W).obj
        (localEvaluationSections p L ev e W hWU i)) :
    ∀ x : (p ⁻¹ᵁ T).toScheme, ∃ i,
      x ∈ nonvanishingLocus (evaluationLineBundle p L T).obj
        (localEvaluationSections p L ev e T (hTW.trans hWU) i) := by
  have ht := mapIsoSections_generate
    (L := (LineBundle.pullback (X.homOfLE (p.preimage_mono hTW))).obj
      (evaluationLineBundle p L W))
    (M := evaluationLineBundle p L T)
    (openPullbackIso L.obj (p.preimage_mono hTW))
    (pullbackSections_generate (X.homOfLE (p.preimage_mono hTW)) hs)
  intro x
  obtain ⟨i, hi⟩ := ht x
  refine ⟨i, ?_⟩
  exact (congrArg (fun σ => x ∈ nonvanishingLocus (evaluationLineBundle p L T).obj σ)
    (localEvaluationSections_restrict p L ev e hTW hWU i)).mp hi

/-- The actual base morphisms on inverse-image opens form the restriction square. -/
lemma evaluationBase_restrict {W T : S.Opens} (hTW : T ≤ W) :
    X.homOfLE (p.preimage_mono hTW) ≫ evaluationBase p W =
      evaluationBase p T ≫ S.homOfLE hTW := by
  apply (cancel_mono W.ι).mp
  simp [evaluationBase, Scheme.Hom.resLE_comp_ι]

/-- Actual local evaluation maps commute with passage to a smaller base open. -/
lemma localEvaluationMap_restrict {U W T : S.Opens} (e : LocalFrame M n U)
    (hTW : T ≤ W) (hWU : W ≤ U)
    (hs : ∀ x : (p ⁻¹ᵁ W).toScheme, ∃ i,
      x ∈ nonvanishingLocus (evaluationLineBundle p L W).obj
        (localEvaluationSections p L ev e W hWU i)) :
    localEvaluationMap p L ev e T (hTW.trans hWU)
        (localEvaluationSections_restrict_generate p L ev e hTW hWU hs) ≫
        RelativeProjectiveSpace.map n (S.homOfLE hTW) =
      X.homOfLE (p.preimage_mono hTW) ≫ localEvaluationMap p L ev e W hWU hs := by
  have ht := relativeLinearSystemMap_mapIso (evaluationBase p T)
    (L := (LineBundle.pullback (X.homOfLE (p.preimage_mono hTW))).obj
      (evaluationLineBundle p L W))
    (M := evaluationLineBundle p L T)
    (openPullbackIso L.obj (p.preimage_mono hTW))
    (pullbackSections_generate (X.homOfLE (p.preimage_mono hTW)) hs)
  have he : mapIsoSections
      (L := (LineBundle.pullback (X.homOfLE (p.preimage_mono hTW))).obj
        (evaluationLineBundle p L W))
      (M := evaluationLineBundle p L T) (openPullbackIso L.obj (p.preimage_mono hTW))
      (fun i => pullbackSection (X.homOfLE (p.preimage_mono hTW))
        (evaluationLineBundle p L W).obj (localEvaluationSections p L ev e W hWU i)) =
      localEvaluationSections p L ev e T (hTW.trans hWU) := by
    funext i
    exact localEvaluationSections_restrict p L ev e hTW hWU i
  simp only [he] at ht
  dsimp only [localEvaluationMap]
  rw [ht]
  exact relativeLinearSystemMap_pullback (evaluationBase p W) (evaluationBase p T)
    (X.homOfLE (p.preimage_mono hTW)) (S.homOfLE hTW)
    (evaluationBase_restrict p hTW) hs

end Langlands.AlgebraicGeometry.ProjectiveBundle
