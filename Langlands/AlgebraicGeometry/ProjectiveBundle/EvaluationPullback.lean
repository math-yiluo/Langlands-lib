import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationTwist
import Langlands.AlgebraicGeometry.ProjectiveBundle.TautologicalRestriction
import Langlands.AlgebraicGeometry.Modules.OpenCoverHomGluing
import Langlands.AlgebraicGeometry.Modules.OpenCoverIsoGluing

/-! # Pulling the global projective degree-one bundle back by evaluation -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.SchemeModule.RigidifiedModule
open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.LinearSystem

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Scheme.Modules

/-- Reversing a commuting square inverts its canonical pullback comparison. -/
lemma squarePullbackIso_reverse {X Y X' Y' : Scheme.{u}}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (s : X' ⟶ X) (t : Y' ⟶ Y)
    (h : p' ≫ t = s ≫ p) (M : Y.Modules) :
    (squarePullbackIso t s p' p h.symm M).hom =
      (squarePullbackIso p p' s t h M).inv := by
  simp [squarePullbackIso, Scheme.Modules.pullbackCongr]

namespace RefinedPullbackComparison

/-- Composing normalized chart comparisons with a compatible local square
preserves restriction on the original source. -/
lemma normalize_local_restrict {X Y U V PU PV : Scheme.{u}}
    (E : X ⟶ Y) (aU : U ⟶ X) (aV : V ⟶ X) (t : U ⟶ V)
    (hta : t ≫ aV = aU)
    (r : U ⟶ PU) (q : V ⟶ PV) (c : PU ⟶ PV)
    (cU : PU ⟶ Y) (cV : PV ⟶ Y)
    (ht : r ≫ c = t ≫ q) (hU : r ≫ cU = aU ≫ E)
    (hV : q ≫ cV = aV ≫ E) (hc : c ≫ cV = cU)
    (G : Y.Modules) {L : X.Modules} {MU : PU.Modules} {MV : PV.Modules}
    (eU : (Scheme.Modules.pullback cU).obj G ≅ MU)
    (eV : (Scheme.Modules.pullback cV).obj G ≅ MV)
    (β : (Scheme.Modules.pullback c).obj MV ≅ MU)
    (he : (Scheme.Modules.pullback c).map eV.hom ≫ β.hom =
      compHom c cV cU hc G ≫ eU.hom)
    (αU : (Scheme.Modules.pullback r).obj MU ⟶ (Scheme.Modules.pullback aU).obj L)
    (αV : (Scheme.Modules.pullback q).obj MV ⟶ (Scheme.Modules.pullback aV).obj L)
    (γ : (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback aV).obj L) ⟶
      (Scheme.Modules.pullback aU).obj L)
    (hα : PullbackSquareCompatible q r t c ht αV αU β.hom γ) :
    (Scheme.Modules.pullback t).map
        (compHom aV E (aV ≫ E) rfl G ≫ (normalize q cV (aV ≫ E) hV eV).hom ≫ αV) ≫ γ =
      compHom t aV aU hta ((Scheme.Modules.pullback E).obj G) ≫
        compHom aU E (aU ≫ E) rfl G ≫ (normalize r cU (aU ≫ E) hU eU).hom ≫ αU := by
  have hp : t ≫ (aV ≫ E) = aU ≫ E := by rw [← Category.assoc, hta]
  have hα' : (Scheme.Modules.pullback t).map αV ≫ γ =
      (squarePullbackIso c t r q ht.symm MV).hom ≫
        (Scheme.Modules.pullback r).map β.hom ≫ αU := by
    rw [squarePullbackIso_reverse q r t c ht MV, hα.eq]
    simp
  have H := normalize_refine t q r c cV (aV ≫ E) cU (aU ≫ E)
    ht.symm hV hc hp hU eV β eU he
  simp only [Functor.map_comp, Category.assoc]
  rw [hα', reassoc_of% H]
  rw [← reassoc_of% (compHom_assoc t aV E aU (aV ≫ E) (aU ≫ E)
    hta rfl rfl hp G)]

end RefinedPullbackComparison

/-- Two restriction laws through the same module morphism imply the canonical
square compatibility on their common source. -/
lemma square_compatible_of_common_restriction {X U V W : Scheme.{u}}
    (a : U ⟶ X) (b : V ⟶ X) (r : W ⟶ U) (s : W ⟶ V) (c : W ⟶ X)
    (hr : r ≫ a = c) (hs : s ≫ b = c)
    {A B : X.Modules}
    (φU : (Scheme.Modules.pullback a).obj A ⟶ (Scheme.Modules.pullback a).obj B)
    (φV : (Scheme.Modules.pullback b).obj A ⟶ (Scheme.Modules.pullback b).obj B)
    (φW : (Scheme.Modules.pullback c).obj A ⟶ (Scheme.Modules.pullback c).obj B)
    (hU : (Scheme.Modules.pullback r).map φU ≫ compHom r a c hr B =
      compHom r a c hr A ≫ φW)
    (hV : (Scheme.Modules.pullback s).map φV ≫ compHom s b c hs B =
      compHom s b c hs A ≫ φW) :
    (Scheme.Modules.pullback r).map φU ≫
        (squarePullbackIso b r s a (hr.trans hs.symm) B).hom =
      (squarePullbackIso b r s a (hr.trans hs.symm) A).hom ≫
        (Scheme.Modules.pullback s).map φV := by
  apply (cancel_mono (compHom s b c hs B)).mp
  rw [Category.assoc, CommonSourceCocycle.square_normalize, hU]
  rw [Category.assoc, hV, ← Category.assoc, CommonSourceCocycle.square_normalize]

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationPullback

/-- Morphisms on inverse images of frame opens glue uniquely when they commute
with restriction to every smaller frame open. -/
lemma existsUnique_hom_of_frameRestriction {X S : Scheme.{u}} (p : X ⟶ S)
    {M : S.Modules} {n : ℕ} (hM : IsLocallyFreeOfRank M (n + 1))
    (A B : X.Modules)
    (φ : ∀ U : FrameOpen M n,
      (Scheme.Modules.pullback (p ⁻¹ᵁ U.val).ι).obj A ⟶
        (Scheme.Modules.pullback (p ⁻¹ᵁ U.val).ι).obj B)
    (hφ : ∀ {U V : FrameOpen M n} (hUV : U ≤ V),
      (Scheme.Modules.pullback (X.homOfLE (p.preimage_mono hUV))).map (φ V) ≫
        compHom (X.homOfLE (p.preimage_mono hUV)) (p ⁻¹ᵁ V.val).ι (p ⁻¹ᵁ U.val).ι
          (X.homOfLE_ι (p.preimage_mono hUV)) B =
      compHom (X.homOfLE (p.preimage_mono hUV)) (p ⁻¹ᵁ V.val).ι (p ⁻¹ᵁ U.val).ι
          (X.homOfLE_ι (p.preimage_mono hUV)) A ≫ φ U) :
    ∃! f : A ⟶ B, ∀ U : FrameOpen M n,
      (Scheme.Modules.pullback (p ⁻¹ᵁ U.val).ι).map f = φ U := by
  let a (U : FrameOpen M n) := (p ⁻¹ᵁ U.val).ι
  have hcover : ∀ x : X, ∃ U : FrameOpen M n, x ∈ (a U).opensRange := by
    intro x
    obtain ⟨U, hx⟩ := exists_frameOpen M n hM (p x)
    exact ⟨U, by simpa only [a, Scheme.Opens.opensRange_ι, Scheme.Hom.mem_preimage] using hx⟩
  have hcompat : ∀ (U V : FrameOpen M n) (P : X.Opens)
      (hU : P ≤ (a U).opensRange) (hV : P ≤ (a V).opensRange),
      OpenCoverHomGluing.transport (a U) (OpenCoverHomGluing.restrictHom (a U) (φ U)) P hU =
        OpenCoverHomGluing.transport (a V) (OpenCoverHomGluing.restrictHom (a V) (φ V)) P hV := by
    intro U V P hU hV
    let W := frameIntersection U V
    let hWU : W ≤ U := frameIntersection_le_left U V
    let hWV : W ≤ V := frameIntersection_le_right U V
    let r := X.homOfLE (p.preimage_mono hWU)
    let s := X.homOfLE (p.preimage_mono hWV)
    have hr : r ≫ a U = a W := X.homOfLE_ι _
    have ht : s ≫ a V = a W := X.homOfLE_ι _
    have H := square_compatible_of_common_restriction (a U) (a V) r s (a W) hr ht
      (φ U) (φ V) (φ W) (hφ hWU) (hφ hWV)
    have hrange : (a U).opensRange ⊓ (a V).opensRange ≤ (r ≫ a U).opensRange := by
      simp only [hr, a, Scheme.Opens.opensRange_ι, W, frameIntersection,
        Scheme.Hom.preimage_inf, le_refl]
    exact OpenCoverHomGluing.transport_compat (a U) (a V) r s (hr.trans ht.symm)
      hrange (φ U) (φ V)
      (OpenCoverHomGluing.conj_square (a V) r s (a U) (hr.trans ht.symm) (φ U) (φ V) H)
      P hU hV
  let D : OpenCoverHomGluing.LocalFamily (fun U => (a U).opensRange) A B :=
    { θ := fun U P hP =>
        OpenCoverHomGluing.transport (a U) (OpenCoverHomGluing.restrictHom (a U) (φ U)) P hP
      nat := fun U P Q hP hQP x => OpenCoverHomGluing.transport_map _ _ P Q hP hQP x
      smul := fun U P hP r x => OpenCoverHomGluing.transport_smul _ _ P hP r x
      compat := hcompat }
  have key : ∀ (U : FrameOpen M n) (W : (p ⁻¹ᵁ U.val).toScheme.Opens),
      (D.hom hcover).app (a U ''ᵁ W) =
        (OpenCoverHomGluing.restrictHom (a U) (φ U)).app W := by
    intro U W
    rw [D.hom_app hcover U _ ((a U).image_le_opensRange W)]
    exact OpenCoverHomGluing.transport_image _ _ W ((a U).image_le_opensRange W)
  refine ⟨D.hom hcover, fun U => OpenCoverHomGluing.pullback_map_eq_of_app _ _ _ (key U), ?_⟩
  intro g hg
  apply OpenCoverHomGluing.hom_ext_of_local hcover
  intro U P hP
  obtain ⟨W, rfl⟩ : ∃ W, P = a U ''ᵁ W :=
    ⟨a U ⁻¹ᵁ P, by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hP]⟩
  rw [key, OpenCoverHomGluing.app_image_eq_of_pullback_map _ g _ (hg U)]

/-- Compatible isomorphisms on the inverse-image frame opens glue uniquely. -/
lemma existsUnique_iso_of_frameRestriction {X S : Scheme.{u}} (p : X ⟶ S)
    {M : S.Modules} {n : ℕ} (hM : IsLocallyFreeOfRank M (n + 1))
    (A B : X.Modules)
    (e : ∀ U : FrameOpen M n,
      (Scheme.Modules.pullback (p ⁻¹ᵁ U.val).ι).obj A ≅
        (Scheme.Modules.pullback (p ⁻¹ᵁ U.val).ι).obj B)
    (he : ∀ {U V : FrameOpen M n} (hUV : U ≤ V),
      (Scheme.Modules.pullback (X.homOfLE (p.preimage_mono hUV))).map (e V).hom ≫
        compHom (X.homOfLE (p.preimage_mono hUV)) (p ⁻¹ᵁ V.val).ι (p ⁻¹ᵁ U.val).ι
          (X.homOfLE_ι (p.preimage_mono hUV)) B =
      compHom (X.homOfLE (p.preimage_mono hUV)) (p ⁻¹ᵁ V.val).ι (p ⁻¹ᵁ U.val).ι
          (X.homOfLE_ι (p.preimage_mono hUV)) A ≫ (e U).hom) :
    ∃! E : A ≅ B, ∀ U : FrameOpen M n,
      (Scheme.Modules.pullback (p ⁻¹ᵁ U.val).ι).map E.hom = (e U).hom := by
  obtain ⟨f, hf, hfunique⟩ :=
    existsUnique_hom_of_frameRestriction p hM A B (fun U => (e U).hom) he
  have hinv : ∀ {U V : FrameOpen M n} (hUV : U ≤ V),
      (Scheme.Modules.pullback (X.homOfLE (p.preimage_mono hUV))).map (e V).inv ≫
        compHom (X.homOfLE (p.preimage_mono hUV)) (p ⁻¹ᵁ V.val).ι (p ⁻¹ᵁ U.val).ι
          (X.homOfLE_ι (p.preimage_mono hUV)) A =
      compHom (X.homOfLE (p.preimage_mono hUV)) (p ⁻¹ᵁ V.val).ι (p ⁻¹ᵁ U.val).ι
          (X.homOfLE_ι (p.preimage_mono hUV)) B ≫ (e U).inv := by
    intro U V hUV
    apply (Iso.inv_comp_eq
      ((Scheme.Modules.pullback (X.homOfLE (p.preimage_mono hUV))).mapIso (e V))).2
    simp only [Functor.mapIso_hom]
    rw [← Category.assoc, he hUV]
    simp
  obtain ⟨g, hg, _⟩ :=
    existsUnique_hom_of_frameRestriction p hM B A (fun U => (e U).inv) hinv
  have inverse_id {C D : X.Modules} (f : C ⟶ D) (g : D ⟶ C)
      (h : ∀ U : FrameOpen M n,
        (Scheme.Modules.pullback (p ⁻¹ᵁ U.val).ι).map f ≫
          (Scheme.Modules.pullback (p ⁻¹ᵁ U.val).ι).map g = 𝟙 _) :
      f ≫ g = 𝟙 C := by
    obtain ⟨q, _, hq⟩ :=
      existsUnique_hom_of_frameRestriction p hM C C (fun _ => 𝟙 _) (by intros; simp)
    apply (hq (f ≫ g) ?_).trans (hq (𝟙 C) ?_).symm
    · intro U
      simpa only [Functor.map_comp] using h U
    · intro U
      simp
  have hfg : f ≫ g = 𝟙 A := inverse_id f g (by
    intro U
    rw [hf U, hg U]
    exact (e U).hom_inv_id)
  have hgf : g ≫ f = 𝟙 B := inverse_id g f (by
    intro U
    rw [hg U, hf U]
    exact (e U).inv_hom_id)
  refine ⟨⟨f, g, hfg, hgf⟩, hf, ?_⟩
  intro E hE
  apply Iso.ext
  exact hfunique E.hom hE

variable {X S : Scheme.{u}} (p : X ⟶ S) {M : S.Modules} (L : LineBundle X)
    (ev : M ⟶ (Scheme.Modules.pushforward p).obj L.obj) {n : ℕ}
    (hM : IsLocallyFreeOfRank M (n + 1)) (hs : FrameEvaluationGenerates p L ev n)

/-- The actual pullback of the global projective degree-one module by evaluation. -/
abbrev source : X.Modules :=
  (Scheme.Modules.pullback (evaluationMap p L ev hM hs)).obj (FrameBundle.twistOne hM).obj

/-- Compare the actual global pullback with the given line bundle on one inverse-image open. -/
def localIso (U : FrameOpen M n) :
    (Scheme.Modules.pullback (p ⁻¹ᵁ U.val).ι).obj (source p L ev hM hs) ≅
      (Scheme.Modules.pullback (p ⁻¹ᵁ U.val).ι).obj L.obj :=
  compIso (p ⁻¹ᵁ U.val).ι (evaluationMap p L ev hM hs)
      ((p ⁻¹ᵁ U.val).ι ≫ evaluationMap p L ev hM hs) rfl (FrameBundle.twistOne hM).obj ≪≫
    RefinedPullbackComparison.normalize (EvaluationTwist.localMap p L ev hs U)
      (FrameBundle.chart hM U) ((p ⁻¹ᵁ U.val).ι ≫ evaluationMap p L ev hM hs)
      (evaluationMap_chart p L ev hM hs U).symm (FrameBundle.twistOneModuleIso hM U) ≪≫
    EvaluationTwist.localIso p L ev hs U

/-- These actual local global-pullback comparisons commute with every frame restriction. -/
lemma localIso_restrict {U V : FrameOpen M n} (hUV : U ≤ V) :
    (Scheme.Modules.pullback (X.homOfLE (p.preimage_mono hUV))).map
        (localIso p L ev hM hs V).hom ≫
          (openPullbackIso L.obj (p.preimage_mono hUV)).hom =
      compHom (X.homOfLE (p.preimage_mono hUV)) (p ⁻¹ᵁ V.val).ι (p ⁻¹ᵁ U.val).ι
        (X.homOfLE_ι (p.preimage_mono hUV)) (source p L ev hM hs) ≫
          (localIso p L ev hM hs U).hom := by
  simp only [localIso, Iso.trans_hom, compIso_hom]
  exact RefinedPullbackComparison.normalize_local_restrict
    (X := X) (Y := frameBundle M n hM)
    (U := (p ⁻¹ᵁ U.val).toScheme) (V := (p ⁻¹ᵁ V.val).toScheme)
    (PU := RelativeProjectiveSpace U.val.toScheme n)
    (PV := RelativeProjectiveSpace V.val.toScheme n)
    (L := L.obj)
    (evaluationMap p L ev hM hs) (p ⁻¹ᵁ U.val).ι (p ⁻¹ᵁ V.val).ι
    (X.homOfLE (p.preimage_mono hUV)) (X.homOfLE_ι (p.preimage_mono hUV))
    (EvaluationTwist.localMap p L ev hs U) (EvaluationTwist.localMap p L ev hs V)
    (FrameBundle.chartMap hM hUV) (FrameBundle.chart hM U) (FrameBundle.chart hM V)
    (EvaluationTwist.localMap_chartMap p L ev hM hs hUV)
    (evaluationMap_chart p L ev hM hs U).symm
    (evaluationMap_chart p L ev hM hs V).symm (FrameBundle.chartMap_chart hM hUV)
    (FrameBundle.twistOne hM).obj
    (FrameBundle.twistOneModuleIso hM U) (FrameBundle.twistOneModuleIso hM V)
    (FrameBundle.chartTwistIso hM hUV) (FrameBundle.twistOneModuleIso_restrict hM hUV)
    (EvaluationTwist.localIso p L ev hs U).hom (EvaluationTwist.localIso p L ev hs V).hom
    (openPullbackIso L.obj (p.preimage_mono hUV)).hom
    (EvaluationTwist.localIso_compatible p L ev hM hs hUV)

/-- The actual local evaluation comparisons glue to a unique global isomorphism. -/
lemma existsUnique_iso :
    ∃! E : source p L ev hM hs ≅ L.obj, ∀ U : FrameOpen M n,
      (Scheme.Modules.pullback (p ⁻¹ᵁ U.val).ι).map E.hom =
        (localIso p L ev hM hs U).hom := by
  apply existsUnique_iso_of_frameRestriction p hM _ _ (localIso p L ev hM hs)
  intro U V hUV
  exact localIso_restrict p L ev hM hs hUV

/-- Evaluation pulls the global projective degree-one module back to the given
line bundle, with no additional compatibility premise. -/
def globalIso : source p L ev hM hs ≅ L.obj :=
  (existsUnique_iso p L ev hM hs).exists.choose

/-- The constructed global isomorphism has the actual local evaluation formula. -/
lemma globalIso_local (U : FrameOpen M n) :
    (Scheme.Modules.pullback (p ⁻¹ᵁ U.val).ι).map (globalIso p L ev hM hs).hom =
      (localIso p L ev hM hs U).hom :=
  (existsUnique_iso p L ev hM hs).exists.choose_spec U

/-- The local formulas uniquely characterize the constructed global comparison. -/
lemma globalIso_unique (E : source p L ev hM hs ≅ L.obj)
    (hE : ∀ U : FrameOpen M n,
      (Scheme.Modules.pullback (p ⁻¹ᵁ U.val).ι).map E.hom =
        (localIso p L ev hM hs U).hom) :
    E = globalIso p L ev hM hs :=
  (existsUnique_iso p L ev hM hs).unique hE (globalIso_local p L ev hM hs)

end Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationPullback
