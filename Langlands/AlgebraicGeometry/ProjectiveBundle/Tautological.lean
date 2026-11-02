import Langlands.AlgebraicGeometry.ProjectiveBundle.FrameBundle
import Langlands.AlgebraicGeometry.ProjectiveBundle.TwistTransition
import Langlands.AlgebraicGeometry.Picard.LineBundleOpenCoverGluing
import Langlands.AlgebraicGeometry.Modules.CommonSourceCocycle
import Langlands.AlgebraicGeometry.Modules.RefinedPullbackComparison

/-! # The degree-one line bundle on the projective frame bundle -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard
open Langlands.Scheme.Modules
open Langlands.SchemeModule.RigidifiedModule

universe u

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma cocycle_of_normalizations {C : Type*} [Category* C]
    {A B B' C₀ C' A' N : C}
    (f : A ⟶ B) (g : B ⟶ B') (h : B' ⟶ C₀) (i : C₀ ⟶ C')
    (j : A ⟶ A') (k : A' ⟶ C')
    (na : A ⟶ N) (nb : B ⟶ N) (nb' : B' ⟶ N)
    (nc : C₀ ⟶ N) (nc' : C' ⟶ N) (na' : A' ⟶ N) [Mono nc']
    (hf : f ≫ nb = na) (hg : g ≫ nb' = nb) (hh : h ≫ nc = nb')
    (hi : i ≫ nc' = nc) (hk : k ≫ nc' = na') (hj : j ≫ na' = na) :
    f ≫ g ≫ h ≫ i = j ≫ k := by
  rw [← cancel_mono nc']
  simp only [Category.assoc]
  rw [hi, hh, hg, hf, hk, hj]

private lemma cocycle_of_normalized_overlaps {T Vab Vbc Vac Ua Ub Uc : Scheme.{u}}
    (t : T ⟶ Vab) (s : T ⟶ Vbc) (r : T ⟶ Vac)
    (fab : Vab ⟶ Ua) (gab : Vab ⟶ Ub) (fbc : Vbc ⟶ Ub) (gbc : Vbc ⟶ Uc)
    (fac : Vac ⟶ Ua) (gac : Vac ⟶ Uc)
    (h₀ : t ≫ fab = r ≫ fac) (h₁ : t ≫ gab = s ≫ fbc)
    (h₂ : s ≫ gbc = r ≫ gac)
    (pa : T ⟶ Ua) (pb : T ⟶ Ub) (pc : T ⟶ Uc)
    (hta : t ≫ fab = pa) (htb : t ≫ gab = pb)
    (hsb : s ≫ fbc = pb) (hsc : s ≫ gbc = pc)
    (hra : r ≫ fac = pa) (hrc : r ≫ gac = pc)
    {Ma : Ua.Modules} {Mb : Ub.Modules} {Mc : Uc.Modules} {P : T.Modules}
    (φab : (Scheme.Modules.pullback fab).obj Ma ≅ (Scheme.Modules.pullback gab).obj Mb)
    (φbc : (Scheme.Modules.pullback fbc).obj Mb ≅ (Scheme.Modules.pullback gbc).obj Mc)
    (φac : (Scheme.Modules.pullback fac).obj Ma ≅ (Scheme.Modules.pullback gac).obj Mc)
    (na : (Scheme.Modules.pullback pa).obj Ma ≅ P)
    (nb : (Scheme.Modules.pullback pb).obj Mb ≅ P)
    (nc : (Scheme.Modules.pullback pc).obj Mc ≅ P)
    (hab : (Scheme.Modules.pullback t).map φab.hom ≫
      compHom t gab pb htb Mb ≫ nb.hom = compHom t fab pa hta Ma ≫ na.hom)
    (hbc : (Scheme.Modules.pullback s).map φbc.hom ≫
      compHom s gbc pc hsc Mc ≫ nc.hom = compHom s fbc pb hsb Mb ≫ nb.hom)
    (hac : (Scheme.Modules.pullback r).map φac.hom ≫
      compHom r gac pc hrc Mc ≫ nc.hom = compHom r fac pa hra Ma ≫ na.hom) :
    (Scheme.Modules.pullback t).map φab.hom ≫
        (squarePullbackIso fbc t s gab h₁ Mb).hom ≫
        (Scheme.Modules.pullback s).map φbc.hom ≫
        (squarePullbackIso gac s r gbc h₂ Mc).hom =
      (squarePullbackIso fac t r fab h₀ Ma).hom ≫
        (Scheme.Modules.pullback r).map φac.hom := by
  have hsqb : (squarePullbackIso fbc t s gab h₁ Mb).hom ≫
      compHom s fbc pb hsb Mb ≫ nb.hom = compHom t gab pb htb Mb ≫ nb.hom := by
    rw [reassoc_of% (CommonSourceCocycle.square_normalize fbc t s gab h₁ Mb pb hsb)]
  have hsqc : (squarePullbackIso gac s r gbc h₂ Mc).hom ≫
      compHom r gac pc hrc Mc ≫ nc.hom = compHom s gbc pc hsc Mc ≫ nc.hom := by
    rw [reassoc_of% (CommonSourceCocycle.square_normalize gac s r gbc h₂ Mc pc hrc)]
  have hsqa : (squarePullbackIso fac t r fab h₀ Ma).hom ≫
      compHom r fac pa hra Ma ≫ na.hom = compHom t fab pa hta Ma ≫ na.hom := by
    rw [reassoc_of% (CommonSourceCocycle.square_normalize fac t r fab h₀ Ma pa hra)]
  exact cocycle_of_normalizations _ _ _ _ _ _ _ _ _ _ _ _
    hab hsqb hbc hsqc hac hsqa

/-- A cocycle on all commuting chart-overlap diagrams supplies the actual
open-cover descent condition. -/
private lemma openCover_cocycle_of_diagrams {X : Scheme.{u}} (𝒱 : X.OpenCover.{u})
    (N : ∀ i, (𝒱.X i).Modules)
    (φ : ∀ i j,
      (Scheme.Modules.pullback (pullback.fst (𝒱.f i) (𝒱.f j))).obj (N i) ≅
        (Scheme.Modules.pullback (pullback.snd (𝒱.f i) (𝒱.f j))).obj (N j))
    (h : ∀ (i j k : 𝒱.I₀) {T : Scheme.{u}}
      (t : T ⟶ pullback (𝒱.f i) (𝒱.f j))
      (s : T ⟶ pullback (𝒱.f j) (𝒱.f k))
      (r : T ⟶ pullback (𝒱.f i) (𝒱.f k))
      (h₀ : t ≫ pullback.fst (𝒱.f i) (𝒱.f j) =
        r ≫ pullback.fst (𝒱.f i) (𝒱.f k))
      (h₁ : t ≫ pullback.snd (𝒱.f i) (𝒱.f j) =
        s ≫ pullback.fst (𝒱.f j) (𝒱.f k))
      (h₂ : s ≫ pullback.snd (𝒱.f j) (𝒱.f k) =
        r ≫ pullback.snd (𝒱.f i) (𝒱.f k)),
      OpenCoverModuleGluing.CompEq4
        ((Scheme.Modules.pullback t).map (φ i j).hom)
        ((squarePullbackIso (pullback.fst (𝒱.f j) (𝒱.f k))
          t s (pullback.snd (𝒱.f i) (𝒱.f j)) h₁ (N j)).hom)
        ((Scheme.Modules.pullback s).map (φ j k).hom)
        ((squarePullbackIso (pullback.snd (𝒱.f i) (𝒱.f k))
          s r (pullback.snd (𝒱.f j) (𝒱.f k)) h₂ (N k)).hom)
        ((squarePullbackIso (pullback.fst (𝒱.f i) (𝒱.f k))
          t r (pullback.fst (𝒱.f i) (𝒱.f j)) h₀ (N i)).hom)
        ((Scheme.Modules.pullback r).map (φ i k).hom)) :
    OpenCoverModuleGluing.CocycleCondition 𝒱 N φ := by
  intro i j k
  apply h


variable {S : Scheme.{u}} {M : S.Modules} {n : ℕ}

/-- The intersection of two frame-bearing opens is frame-bearing. -/
abbrev frameIntersection (U V : FrameOpen M n) : FrameOpen M n :=
  ⟨U.val ⊓ V.val, ⟨(frame M n U).restrict inf_le_left⟩⟩

lemma frameIntersection_le_left (U V : FrameOpen M n) : frameIntersection U V ≤ U :=
  (inf_le_left : U.val ⊓ V.val ≤ U.val)

lemma frameIntersection_le_right (U V : FrameOpen M n) : frameIntersection U V ≤ V :=
  (inf_le_right : U.val ⊓ V.val ≤ V.val)

lemma le_frameIntersection {L U V : FrameOpen M n} (hU : L ≤ U) (hV : L ≤ V) :
    L ≤ frameIntersection U V :=
  (le_inf hU hV : L.val ≤ U.val ⊓ V.val)

/-- A frame-bearing open contained in three specified frame opens. -/
abbrev frameTripleIntersection (U V W : FrameOpen M n) : FrameOpen M n :=
  frameIntersection (frameIntersection U V) W

lemma frameTriple_le_first (U V W : FrameOpen M n) :
    frameTripleIntersection U V W ≤ U :=
  (frameIntersection_le_left (frameIntersection U V) W).trans
    (frameIntersection_le_left U V)

lemma frameTriple_le_middle (U V W : FrameOpen M n) :
    frameTripleIntersection U V W ≤ V :=
  (frameIntersection_le_left (frameIntersection U V) W).trans
    (frameIntersection_le_right U V)

lemma frameTriple_le_last (U V W : FrameOpen M n) :
    frameTripleIntersection U V W ≤ W :=
  frameIntersection_le_right (frameIntersection U V) W

namespace CoordinateCocycle

variable {𝒰 : S.OpenCover} [Category* 𝒰.I₀] [𝒰.LocallyDirected]
  [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] (d : CoordinateCocycle n 𝒰)

/-- Each chart has exactly the inverse image of its base chart as its range. -/
lemma chart_opensRange (i : 𝒰.I₀) :
    (d.chart i).opensRange = d.toBase ⁻¹ᵁ (𝒰.f i).opensRange :=
  (d.relativeGluingData.toBase_preimage_eq_opensRange_ι i).symm


omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- Composition packaged with the generalized canonical comparison. -/
lemma chartTwistIso_compHom {i j k : 𝒰.I₀} (a : i ⟶ j) (b : j ⟶ k) :
    (Scheme.Modules.pullback (d.chartFunctor.map a)).map (d.chartTwistIso b).hom ≫
        (d.chartTwistIso a).hom =
      compHom (X := d.chartFunctor.obj i) (Y := d.chartFunctor.obj j)
        (Z := d.chartFunctor.obj k)
        (d.chartFunctor.map a) (d.chartFunctor.map b) (d.chartFunctor.map (a ≫ b))
        (d.chartMap_comp a b) (RelativeProjectiveSpace.twistOne (𝒰.X k) n).obj ≫
      (d.chartTwistIso (a ≫ b)).hom := by
  unfold compHom
  rw [Category.assoc]
  exact d.chartTwistIso_comp a b

/-- Coherent chart transitions preserve normalization along composable chart arrows. -/
abbrev chartTransition_normalize {T V : Scheme.{u}} {i j k l : 𝒰.I₀}
    (t : T ⟶ V) (q : V ⟶ d.chartFunctor.obj j)
    (r : T ⟶ d.chartFunctor.obj i) (c : i ⟶ j) (a : j ⟶ k) (b : j ⟶ l)
    (f : V ⟶ d.chartFunctor.obj k) (g : V ⟶ d.chartFunctor.obj l)
    (p : T ⟶ d.chartFunctor.obj k) (s : T ⟶ d.chartFunctor.obj l)
    (ht : t ≫ q = r ≫ d.chartFunctor.map c)
    (hf : q ≫ d.chartFunctor.map a = f) (hg : q ≫ d.chartFunctor.map b = g)
    (hp : t ≫ f = p) (hs : t ≫ g = s)
    (hp' : r ≫ d.chartFunctor.map (c ≫ a) = p)
    (hs' : r ≫ d.chartFunctor.map (c ≫ b) = s) :=
  RefinedPullbackComparison.transition_normalize
    (K := d.chartFunctor.obj j) (L := d.chartFunctor.obj i)
    (A := d.chartFunctor.obj k) (B := d.chartFunctor.obj l)
    t q r (d.chartFunctor.map c) (d.chartFunctor.map a) (d.chartFunctor.map b)
    f g (d.chartFunctor.map (c ≫ a)) (d.chartFunctor.map (c ≫ b)) p s
    ht hf hg (d.chartMap_comp c a) (d.chartMap_comp c b) hp hs hp' hs'
    (d.chartTwistIso a) (d.chartTwistIso b) (d.chartTwistIso c)
    (d.chartTwistIso (c ≫ a)) (d.chartTwistIso (c ≫ b))
    (d.chartTwistIso_compHom c a) (d.chartTwistIso_compHom c b)


end CoordinateCocycle

namespace FrameBundle

variable (hM : IsLocallyFreeOfRank M (n + 1))

/-- A projective restriction, including its actual change of frame. -/
abbrev chartMap {U V : FrameOpen M n} (h : U ≤ V) :
    RelativeProjectiveSpace U.val.toScheme n ⟶
      RelativeProjectiveSpace V.val.toScheme n :=
  (frameCocycle M n hM).chartFunctor.map (homOfLE h)

instance {U V : FrameOpen M n} (h : U ≤ V) : IsOpenImmersion (chartMap hM h) :=
  inferInstanceAs (IsOpenImmersion
    ((frameCocycle M n hM).relativeGluingData.functor.map (homOfLE h)))

@[reassoc (attr := simp)]
lemma chartMap_chart {U V : FrameOpen M n} (h : U ≤ V) :
    chartMap hM h ≫ chart hM V = chart hM U :=
  (frameCocycle M n hM).transition_chart (homOfLE h)

@[reassoc (attr := simp)]
lemma chartMap_comp {U V W : FrameOpen M n} (hUV : U ≤ V) (hVW : V ≤ W) :
    chartMap hM hUV ≫ chartMap hM hVW = chartMap hM (hUV.trans hVW) :=
  (frameCocycle M n hM).chartMap_comp (homOfLE hUV) (homOfLE hVW)

/-- The two projective chart ranges meet in the chart of the intersection. -/
lemma chart_intersection_opensRange (U V : FrameOpen M n) :
    (chart hM (frameIntersection U V)).opensRange =
      (chart hM U).opensRange ⊓ (chart hM V).opensRange := by
  change ((frameCocycle M n hM).chart (frameIntersection U V)).opensRange =
    ((frameCocycle M n hM).chart U).opensRange ⊓
      ((frameCocycle M n hM).chart V).opensRange
  simp only [CoordinateCocycle.chart_opensRange, frameCover,
    Scheme.Opens.opensRange_ι, frameIntersection, Scheme.Hom.preimage_inf]

/-- The chart of the intersection is the actual pullback of the two charts. -/
lemma isPullback_intersection (U V : FrameOpen M n) :
    IsPullback
      (chartMap hM (show frameIntersection U V ≤ U from (inf_le_left : U.val ⊓ V.val ≤ U.val)))
      (chartMap hM (show frameIntersection U V ≤ V from (inf_le_right : U.val ⊓ V.val ≤ V.val)))
      (chart hM U) (chart hM V) := by
  apply IsOpenImmersion.isPullback
  · simp
  · apply (chart hM V).image_injective
    dsimp only
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      ← Scheme.Hom.opensRange_comp]
    simp only [chartMap_chart, chart_intersection_opensRange]
    exact inf_comm _ _

/-- The canonical identification of a genuine overlap with the intersection chart. -/
def intersectionIso (U V : FrameOpen M n) :
    RelativeProjectiveSpace (frameIntersection U V).val.toScheme n ≅
      pullback (chart hM U) (chart hM V) :=
  (isPullback_intersection hM U V).isoPullback

@[reassoc (attr := simp)]
lemma intersectionIso_hom_fst (U V : FrameOpen M n) :
    (intersectionIso hM U V).hom ≫ pullback.fst (chart hM U) (chart hM V) =
      chartMap hM (show frameIntersection U V ≤ U from (inf_le_left : U.val ⊓ V.val ≤ U.val)) :=
  (isPullback_intersection hM U V).isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma intersectionIso_hom_snd (U V : FrameOpen M n) :
    (intersectionIso hM U V).hom ≫ pullback.snd (chart hM U) (chart hM V) =
      chartMap hM (show frameIntersection U V ≤ V from (inf_le_right : U.val ⊓ V.val ≤ V.val)) :=
  (isPullback_intersection hM U V).isoPullback_hom_snd

@[reassoc (attr := simp)]
lemma intersectionIso_inv_fst (U V : FrameOpen M n) :
    (intersectionIso hM U V).inv ≫
        chartMap hM (show frameIntersection U V ≤ U from (inf_le_left : U.val ⊓ V.val ≤ U.val)) =
      pullback.fst (chart hM U) (chart hM V) :=
  (isPullback_intersection hM U V).isoPullback_inv_fst

@[reassoc (attr := simp)]
lemma intersectionIso_inv_snd (U V : FrameOpen M n) :
    (intersectionIso hM U V).inv ≫
        chartMap hM (show frameIntersection U V ≤ V from (inf_le_right : U.val ⊓ V.val ≤ V.val)) =
      pullback.snd (chart hM U) (chart hM V) :=
  (isPullback_intersection hM U V).isoPullback_inv_snd

/-- Three maps agreeing in the global scheme factor through one intersection chart. -/
lemma exists_tripleChartLift {T : Scheme.{u}} (U V W : FrameOpen M n)
    (a : T ⟶ RelativeProjectiveSpace U.val.toScheme n)
    (b : T ⟶ RelativeProjectiveSpace V.val.toScheme n)
    (c : T ⟶ RelativeProjectiveSpace W.val.toScheme n)
    (hab : a ≫ chart hM U = b ≫ chart hM V)
    (hbc : b ≫ chart hM V = c ≫ chart hM W) :
    ∃ q : T ⟶ RelativeProjectiveSpace (frameTripleIntersection U V W).val.toScheme n,
      q ≫ chartMap hM (frameTriple_le_first U V W) = a ∧
      q ≫ chartMap hM (frameTriple_le_middle U V W) = b ∧
      q ≫ chartMap hM (frameTriple_le_last U V W) = c := by
  obtain ⟨r, hra, hrb⟩ := (isPullback_intersection hM U V).exists_lift a b hab
  have hr : r ≫ chart hM (frameIntersection U V) = c ≫ chart hM W := by
    calc
      _ = r ≫ chartMap hM (frameIntersection_le_left U V) ≫ chart hM U := by
        rw [chartMap_chart]
      _ = a ≫ chart hM U := by rw [← Category.assoc, hra]
      _ = _ := hab.trans hbc
  obtain ⟨q, hqr, hqc⟩ :=
    (isPullback_intersection hM (frameIntersection U V) W).exists_lift r c hr
  refine ⟨q, ?_, ?_, hqc⟩
  · rw [← chartMap_comp hM (frameIntersection_le_left (frameIntersection U V) W)
      (frameIntersection_le_left U V), ← Category.assoc, hqr, hra]
  · rw [← chartMap_comp hM (frameIntersection_le_left (frameIntersection U V) W)
      (frameIntersection_le_right U V), ← Category.assoc, hqr, hrb]

/-- The actual degree-one line bundle on a projective frame chart. -/
abbrev chartTwist (U : FrameOpen M n) :=
  RelativeProjectiveSpace.twistOne ((frameCover M n hM).X U) n

/-- The coherent degree-one comparison for a projective frame restriction. -/
abbrev chartTwistIso {U V : FrameOpen M n} (h : U ≤ V) :=
  (frameCocycle M n hM).chartTwistIso (homOfLE h)

/-- Composition of frame-chart comparisons uses the canonical pullback associator. -/
abbrev chartTwistIso_comp {U V W : FrameOpen M n} (hUV : U ≤ V) (hVW : V ≤ W) :=
  (frameCocycle M n hM).chartTwistIso_compHom (homOfLE hUV) (homOfLE hVW)

/-- The actual degree-one comparison on an ordered pairwise overlap. -/
def overlapTwistIso (U V : FrameOpen M n) :
    (Scheme.Modules.pullback (pullback.fst (chart hM U) (chart hM V))).obj
        (chartTwist hM U).obj ≅
      (Scheme.Modules.pullback (pullback.snd (chart hM U) (chart hM V))).obj
        (chartTwist hM V).obj :=
  RefinedPullbackComparison.transition (intersectionIso hM U V).inv
    (chartMap hM (frameIntersection_le_left U V))
    (chartMap hM (frameIntersection_le_right U V))
    (pullback.fst (chart hM U) (chart hM V))
    (pullback.snd (chart hM U) (chart hM V))
    (intersectionIso_inv_fst hM U V) (intersectionIso_inv_snd hM U V)
    (chartTwistIso hM (frameIntersection_le_left U V))
    (chartTwistIso hM (frameIntersection_le_right U V))

/-- Compare a pulled-back chart twist with the twist on a chosen smaller chart. -/
abbrev twistNormalize {T : Scheme.{u}} {L U : FrameOpen M n}
    (q : T ⟶ RelativeProjectiveSpace L.val.toScheme n) (h : L ≤ U)
    (p : T ⟶ RelativeProjectiveSpace U.val.toScheme n) (hp : q ≫ chartMap hM h = p) :=
  RefinedPullbackComparison.normalize q (chartMap hM h) p hp (chartTwistIso hM h)

/-- The overlap comparison preserves normalization on any common smaller chart. -/
lemma overlapTwistIso_normalize {T : Scheme.{u}} (U V L : FrameOpen M n)
    (hLU : L ≤ U) (hLV : L ≤ V)
    (t : T ⟶ pullback (chart hM U) (chart hM V))
    (q : T ⟶ RelativeProjectiveSpace L.val.toScheme n)
    (p : T ⟶ RelativeProjectiveSpace U.val.toScheme n)
    (s : T ⟶ RelativeProjectiveSpace V.val.toScheme n)
    (htp : t ≫ pullback.fst (chart hM U) (chart hM V) = p)
    (hts : t ≫ pullback.snd (chart hM U) (chart hM V) = s)
    (hp : q ≫ chartMap hM hLU = p) (hs : q ≫ chartMap hM hLV = s) :
    (Scheme.Modules.pullback t).map (overlapTwistIso hM U V).hom ≫
        compHom t (pullback.snd (chart hM U) (chart hM V)) s hts (chartTwist hM V).obj ≫
          (twistNormalize hM q hLV s hs).hom =
      compHom t (pullback.fst (chart hM U) (chart hM V)) p htp (chartTwist hM U).obj ≫
        (twistNormalize hM q hLU p hp).hom := by
  have ht : t ≫ (intersectionIso hM U V).inv =
      q ≫ chartMap hM (le_frameIntersection hLU hLV) := by
    apply (cancel_mono (chartMap hM (frameIntersection_le_left U V))).mp
    simp only [Category.assoc, intersectionIso_inv_fst, chartMap_comp, htp, hp]
  have H := (frameCocycle M n hM).chartTransition_normalize
    t (intersectionIso hM U V).inv q
    (homOfLE (le_frameIntersection hLU hLV))
    (homOfLE (frameIntersection_le_left U V))
    (homOfLE (frameIntersection_le_right U V))
    (pullback.fst (chart hM U) (chart hM V))
    (pullback.snd (chart hM U) (chart hM V)) p s ht
    (intersectionIso_inv_fst hM U V) (intersectionIso_inv_snd hM U V)
    htp hts hp hs
  dsimp only [overlapTwistIso, twistNormalize, chartMap, chartTwistIso]
  exact H

/-- The actual overlap comparisons satisfy the cocycle on every commuting
diagram of three overlaps, including repeated charts. -/
lemma overlapTwistIso_cocycle {T : Scheme.{u}} (U V W : FrameOpen M n)
    (t : T ⟶ pullback (chart hM U) (chart hM V))
    (s : T ⟶ pullback (chart hM V) (chart hM W))
    (r : T ⟶ pullback (chart hM U) (chart hM W))
    (h₀ : t ≫ pullback.fst (chart hM U) (chart hM V) =
      r ≫ pullback.fst (chart hM U) (chart hM W))
    (h₁ : t ≫ pullback.snd (chart hM U) (chart hM V) =
      s ≫ pullback.fst (chart hM V) (chart hM W))
    (h₂ : s ≫ pullback.snd (chart hM V) (chart hM W) =
      r ≫ pullback.snd (chart hM U) (chart hM W)) :
    OpenCoverModuleGluing.CompEq4
      ((Scheme.Modules.pullback t).map (overlapTwistIso hM U V).hom)
      ((squarePullbackIso (pullback.fst (chart hM V) (chart hM W))
        t s (pullback.snd (chart hM U) (chart hM V)) h₁ (chartTwist hM V).obj).hom)
      ((Scheme.Modules.pullback s).map (overlapTwistIso hM V W).hom)
      ((squarePullbackIso (pullback.snd (chart hM U) (chart hM W))
        s r (pullback.snd (chart hM V) (chart hM W)) h₂ (chartTwist hM W).obj).hom)
      ((squarePullbackIso (pullback.fst (chart hM U) (chart hM W))
        t r (pullback.fst (chart hM U) (chart hM V)) h₀ (chartTwist hM U).obj).hom)
      ((Scheme.Modules.pullback r).map (overlapTwistIso hM U W).hom) := by
  apply OpenCoverModuleGluing.CompEq4.of_eq
  let pa := t ≫ pullback.fst (chart hM U) (chart hM V)
  let pb := t ≫ pullback.snd (chart hM U) (chart hM V)
  let pc := s ≫ pullback.snd (chart hM V) (chart hM W)
  have hab : pa ≫ chart hM U = pb ≫ chart hM V := by
    dsimp only [pa, pb]
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hbc : pb ≫ chart hM V = pc ≫ chart hM W := by
    dsimp only [pb, pc]
    rw [h₁, Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨q, hqa, hqb, hqc⟩ := exists_tripleChartLift hM U V W pa pb pc hab hbc
  let L := frameTripleIntersection U V W
  let ha := frameTriple_le_first U V W
  let hb := frameTriple_le_middle U V W
  let hc := frameTriple_le_last U V W
  exact cocycle_of_normalized_overlaps t s r _ _ _ _ _ _ h₀ h₁ h₂ pa pb pc
    rfl rfl h₁.symm rfl h₀.symm h₂.symm
    (overlapTwistIso hM U V) (overlapTwistIso hM V W) (overlapTwistIso hM U W)
    (twistNormalize hM q ha pa hqa) (twistNormalize hM q hb pb hqb)
    (twistNormalize hM q hc pc hqc)
    (overlapTwistIso_normalize hM U V L ha hb t q pa pb rfl rfl hqa hqb)
    (overlapTwistIso_normalize hM V W L hb hc s q pb pc h₁.symm rfl hqb hqc)
    (overlapTwistIso_normalize hM U W L ha hc r q pa pc h₀.symm h₂.symm hqa hqc)

/-- The existing projective frame cover, presented with its chart maps explicitly. -/
abbrev chartCover : (frameBundle M n hM).OpenCover where
  I₀ := FrameOpen M n
  X U := RelativeProjectiveSpace ((frameCover M n hM).X U) n
  f U := chart hM U
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun U ↦ inferInstance⟩
    obtain ⟨U, y, hy⟩ := (openCover hM).exists_eq x
    exact ⟨U, y, hy⟩

/-- The twist comparisons obey descent on the actual triple scheme pullbacks. -/
abbrev overlapTwistIso_openCover_cocycle :=
  openCover_cocycle_of_diagrams (chartCover hM)
    (fun U ↦ (chartTwist hM U).obj) (overlapTwistIso hM)
    (fun U V W {T} t s r h₀ h₁ h₂ ↦
      overlapTwistIso_cocycle hM (T := T) U V W t s r h₀ h₁ h₂)

/-- The degree-one line bundles and their proved actual-overlap descent data. -/
def twistGluingData : LineBundleGluingData (chartCover hM) where
  bundle := chartTwist hM
  transition := overlapTwistIso hM
  cocycle := overlapTwistIso_openCover_cocycle hM

/-- The actual degree-one line bundle on the glued projective frame scheme. -/
def twistOne : LineBundle (frameBundle M n hM) :=
  (twistGluingData hM).glue

/-- The global degree-one line bundle pulls back to the actual twist on each chart. -/
def twistOnePullbackIso (U : FrameOpen M n) :
    (LineBundle.pullback (chart hM U)).obj (twistOne hM) ≅ chartTwist hM U :=
  (twistGluingData hM).iso U

/-- The underlying module comparison with a chart's actual degree-one twist. -/
def twistOneModuleIso (U : FrameOpen M n) :
    (Scheme.Modules.pullback (chart hM U)).obj (twistOne hM).obj ≅
      (chartTwist hM U).obj :=
  (twistGluingData hM).moduleIso U

/-- The chart comparisons realize the prescribed change of frame on every overlap. -/
lemma twistOneModuleIso_compatible (U V : FrameOpen M n) :
    (Scheme.Modules.pullback (pullback.fst (chart hM U) (chart hM V))).map
        (twistOneModuleIso hM U).hom ≫ (overlapTwistIso hM U V).hom =
      (squarePullbackIso (chart hM V)
        (pullback.fst (chart hM U) (chart hM V))
        (pullback.snd (chart hM U) (chart hM V))
        (chart hM U) pullback.condition (twistOne hM).obj).hom ≫
          (Scheme.Modules.pullback (pullback.snd (chart hM U) (chart hM V))).map
            (twistOneModuleIso hM V).hom :=
  (twistGluingData hM).moduleIso_compatible U V

end FrameBundle

end Langlands.AlgebraicGeometry.ProjectiveBundle
