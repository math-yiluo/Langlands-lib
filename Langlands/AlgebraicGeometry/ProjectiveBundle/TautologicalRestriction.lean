import Langlands.AlgebraicGeometry.ProjectiveBundle.Tautological
import Langlands.AlgebraicGeometry.Modules.CommonSourceTransitionTransport

/-! # Restriction of the global projective degree-one comparison -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule.RigidifiedModule

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Scheme.Modules.RefinedPullbackComparison

/-- An identity refinement only inserts the canonical identity pullback. -/
lemma normalize_id_left {K A : Scheme.{u}} (a : K ⟶ A)
    {M : A.Modules} {N : K.Modules}
    (e : (Scheme.Modules.pullback a).obj M ≅ N) :
    (normalize (𝟙 K) a a (Category.id_comp a) e).hom =
      e.hom ≫ (Scheme.Modules.pullbackId K).inv.app N := by
  simp only [normalize, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom]
  rw [← cancel_mono ((Scheme.Modules.pullbackId K).hom.app N)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [NatTrans.naturality, Functor.id_map]
  have hc : (Scheme.Modules.pullbackId K).hom.app ((Scheme.Modules.pullback a).obj M) =
      compHom (𝟙 K) a a (Category.id_comp a) M := by
    simpa using (compHom_id_left a a (Category.id_comp a) M).symm
  rw [hc]
  simp

/-- A normalized identity chart comparison is the identity on its pullback. -/
lemma normalize_identity {K : Scheme.{u}} (a : K ⟶ K) (ha : a = 𝟙 K)
    (M : K.Modules) (e : (Scheme.Modules.pullback a).obj M ≅ M)
    (he : e.hom = (Scheme.Modules.pullbackCongr ha).hom.app M ≫
      (Scheme.Modules.pullbackId K).hom.app M) :
    (normalize (𝟙 K) a (𝟙 K) (by rw [ha, Category.id_comp]) e).hom =
      𝟙 ((Scheme.Modules.pullback (𝟙 K)).obj M) := by
  subst a
  have he' : e.hom = (Scheme.Modules.pullbackId K).hom.app M := by
    simpa [Scheme.Modules.pullbackCongr] using he
  rw [normalize_id_left, he']
  exact Iso.hom_inv_id_app _ _

end Langlands.Scheme.Modules.RefinedPullbackComparison

namespace Langlands.Scheme.Modules

/-- Actual overlap descent and a normalized overlap determine restriction. -/
lemma restriction_of_normalized_overlap {X U V O : Scheme.{u}}
    (a : U ⟶ X) (b : V ⟶ X) (c : U ⟶ V) (hc : c ≫ b = a)
    (f : O ⟶ U) (g : O ⟶ V) (w : f ≫ a = g ≫ b)
    (t : U ⟶ O) (hf : t ≫ f = 𝟙 U) (hg : t ≫ g = c)
    (G : X.Modules) {M : U.Modules} {N : V.Modules}
    (ea : (Scheme.Modules.pullback a).obj G ≅ M)
    (eb : (Scheme.Modules.pullback b).obj G ≅ N)
    (e : (Scheme.Modules.pullback c).obj N ≅ M)
    (φ : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback g).obj N)
    (hφ : (Scheme.Modules.pullback f).map ea.hom ≫ φ.hom =
      (squarePullbackIso b f g a w G).hom ≫ (Scheme.Modules.pullback g).map eb.hom)
    (hn : (Scheme.Modules.pullback t).map φ.hom ≫ compHom t g c hg N ≫ e.hom =
      compHom t f (𝟙 U) hf M ≫ (Scheme.Modules.pullbackId U).hom.app M) :
    (Scheme.Modules.pullback c).map eb.hom ≫ e.hom =
      compHom c b a hc G ≫ ea.hom := by
  have hw : (𝟙 U) ≫ a = c ≫ b := by simp only [Category.id_comp, hc]
  have hφeq : φ = CommonSourceCocycle.transition f g a b w G ea eb := by
    ext1
    rw [← cancel_epi ((Scheme.Modules.pullback f).map ea.hom), hφ]
    simp only [CommonSourceCocycle.transition, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, ← Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have ht := CommonSourceCocycle.transport_transition t f g (𝟙 U) c hf hg a b w hw G ea eb
  rw [← hφeq] at ht
  have H : (CommonSourceCocycle.transport t f g (𝟙 U) c hf hg φ).hom ≫ e.hom =
      (Scheme.Modules.pullbackId U).hom.app M := by
    simp only [CommonSourceCocycle.transport, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom]
    rw [← cancel_epi (compIso t f (𝟙 U) hf M).hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [compIso_hom, compIso_hom]
    exact hn
  rw [ht] at H
  have H' := congrArg (fun k ↦ (Scheme.Modules.pullback (𝟙 U)).map ea.hom ≫ k) H
  simp only [CommonSourceCocycle.transition, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp] at H'
  have hs := CommonSourceCocycle.square_normalize b (𝟙 U) c a hw G a hc
  have hu : compHom (𝟙 U) a a (hw.trans hc) G =
      (Scheme.Modules.pullbackId U).hom.app ((Scheme.Modules.pullback a).obj G) := by
    simpa using compHom_id_left a a (hw.trans hc) G
  rw [hu] at hs
  apply (cancel_epi (squarePullbackIso b (𝟙 U) c a hw G).hom).mp
  rw [reassoc_of% hs]
  exact H'.trans ((Scheme.Modules.pullbackId U).hom.naturality ea.hom)

end Langlands.Scheme.Modules

namespace Langlands.AlgebraicGeometry.ProjectiveBundle.FrameBundle

variable {S : Scheme.{u}} {M : S.Modules} {n : ℕ}
    (hM : Langlands.Scheme.Modules.IsLocallyFreeOfRank M (n + 1))

/-- A reflexive frame restriction is the identity scheme map. -/
lemma chartMap_id (U : FrameOpen M n) :
    chartMap hM (show U ≤ U from le_rfl) =
      𝟙 (RelativeProjectiveSpace U.val.toScheme n) :=
  (frameCocycle M n hM).chartMap_id U

/-- Normalizing along the identity frame restriction fixes the actual pullback. -/
lemma twistNormalize_id (U : FrameOpen M n) :
    (twistNormalize hM (𝟙 (RelativeProjectiveSpace U.val.toScheme n))
      (show U ≤ U from le_rfl) (𝟙 (RelativeProjectiveSpace U.val.toScheme n))
      (by rw [chartMap_id, Category.id_comp])).hom =
      𝟙 ((Scheme.Modules.pullback (𝟙 (RelativeProjectiveSpace U.val.toScheme n))).obj
        (chartTwist hM U).obj) := by
  exact RefinedPullbackComparison.normalize_identity _ (chartMap_id hM U)
    (chartTwist hM U).obj (chartTwistIso hM (show U ≤ U from le_rfl))
    ((frameCocycle M n hM).chartTwistIso_id U)

/-- Normalize the actual overlap on the smaller of two nested frame charts. -/
lemma overlapTwistIso_restrict_normalize {U V : FrameOpen M n} (hUV : U ≤ V) :
    (Scheme.Modules.pullback
      (pullback.lift (𝟙 (RelativeProjectiveSpace U.val.toScheme n)) (chartMap hM hUV)
        (by simp))).map (overlapTwistIso hM U V).hom ≫
      compHom _ (pullback.snd (chart hM U) (chart hM V)) (chartMap hM hUV)
        (pullback.lift_snd _ _ _) (chartTwist hM V).obj ≫ (chartTwistIso hM hUV).hom =
    compHom _ (pullback.fst (chart hM U) (chart hM V))
      (𝟙 (RelativeProjectiveSpace U.val.toScheme n)) (pullback.lift_fst _ _ _)
        (chartTwist hM U).obj ≫
      (Scheme.Modules.pullbackId (RelativeProjectiveSpace U.val.toScheme n)).hom.app
        (chartTwist hM U).obj := by
  let t := pullback.lift (𝟙 (RelativeProjectiveSpace U.val.toScheme n)) (chartMap hM hUV)
    (by simp : 𝟙 _ ≫ chart hM U = chartMap hM hUV ≫ chart hM V)
  have H := overlapTwistIso_normalize hM U V U le_rfl hUV t (𝟙 _)
    (𝟙 _) (chartMap hM hUV) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (by rw [chartMap_id, Category.id_comp]) (Category.id_comp _)
  rw [twistNormalize_id] at H
  change (Scheme.Modules.pullback t).map (overlapTwistIso hM U V).hom ≫
      compHom t _ _ _ (chartTwist hM V).obj ≫
        (RefinedPullbackComparison.normalize (𝟙 _) (chartMap hM hUV)
          (chartMap hM hUV) (Category.id_comp _) (chartTwistIso hM hUV)).hom = _ at H
  rw [RefinedPullbackComparison.normalize_id_left] at H
  have H' := congrArg (fun k ↦ k ≫
    (Scheme.Modules.pullbackId (RelativeProjectiveSpace U.val.toScheme n)).hom.app
      (chartTwist hM U).obj) H
  dsimp only [chartTwist, Functor.id_obj] at H'
  simpa only [Category.assoc, Iso.inv_hom_id_app, Functor.id_obj, Category.comp_id] using H'

/-- The global degree-one chart comparisons commute with every full frame restriction. -/
lemma twistOneModuleIso_restrict {U V : FrameOpen M n} (hUV : U ≤ V) :
    (Scheme.Modules.pullback (chartMap hM hUV)).map (twistOneModuleIso hM V).hom ≫
      (chartTwistIso hM hUV).hom =
    compHom (chartMap hM hUV) (chart hM V) (chart hM U)
      (chartMap_chart hM hUV) (twistOne hM).obj ≫ (twistOneModuleIso hM U).hom := by
  exact restriction_of_normalized_overlap
    (X := frameBundle M n hM)
    (U := RelativeProjectiveSpace U.val.toScheme n)
    (V := RelativeProjectiveSpace V.val.toScheme n)
    (O := pullback (chart hM U) (chart hM V))
    (chart hM U) (chart hM V) (chartMap hM hUV) (chartMap_chart hM hUV)
    (pullback.fst _ _) (pullback.snd _ _) pullback.condition
    (pullback.lift (𝟙 _) (chartMap hM hUV) (by simp))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (twistOne hM).obj
    (twistOneModuleIso hM U) (twistOneModuleIso hM V) (chartTwistIso hM hUV)
    (overlapTwistIso hM U V) (twistOneModuleIso_compatible hM U V)
    (overlapTwistIso_restrict_normalize hM hUV)

/-- Restrict the larger chart comparison and then use the full degree-one transition. -/
def twistOneRestrictionIso {U V : FrameOpen M n} (hUV : U ≤ V) :
    (Scheme.Modules.pullback (chartMap hM hUV)).obj
        ((Scheme.Modules.pullback (chart hM V)).obj (twistOne hM).obj) ≅
      (chartTwist hM U).obj :=
  (Scheme.Modules.pullback (chartMap hM hUV)).mapIso (twistOneModuleIso hM V) ≪≫
    chartTwistIso hM hUV

/-- The nested-chart comparison is the canonical composition comparison followed
by the smaller chart's comparison. -/
lemma twistOneRestrictionIso_hom {U V : FrameOpen M n} (hUV : U ≤ V) :
    (twistOneRestrictionIso hM hUV).hom =
      compHom (chartMap hM hUV) (chart hM V) (chart hM U)
        (chartMap_chart hM hUV) (twistOne hM).obj ≫ (twistOneModuleIso hM U).hom :=
  twistOneModuleIso_restrict hM hUV

end Langlands.AlgebraicGeometry.ProjectiveBundle.FrameBundle
