import Langlands.AlgebraicGeometry.ProjectiveBundle.FrameAtlasTwist
import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationPullback

/-! # Restriction of degree-one comparisons on genuine frame atlases -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.SchemeModule.RigidifiedModule
open Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.RelativeProjectiveSpace

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.LinearSystem

/-- A compatible square stays compatible when its two paths are exchanged. -/
lemma PullbackSquareCompatible.reverse {X Y X' Y' : Scheme.{u}}
    {N : X.Modules} {M : Y.Modules} {N' : X'.Modules} {M' : Y'.Modules}
    {p : X ⟶ Y} {p' : X' ⟶ Y'} {a : X' ⟶ X} {b : Y' ⟶ Y}
    {w : p' ≫ b = a ≫ p}
    {δ : (Scheme.Modules.pullback p).obj M ⟶ N}
    {α : (Scheme.Modules.pullback p').obj M' ⟶ N'}
    {β : (Scheme.Modules.pullback b).obj M ⟶ M'}
    {γ : (Scheme.Modules.pullback a).obj N ⟶ N'}
    (h : PullbackSquareCompatible p p' a b w δ α β γ) :
    PullbackSquareCompatible b a p' p w.symm β γ δ α := by
  unfold PullbackSquareCompatible
  rw [squarePullbackIso_reverse p p' a b w M, h.eq]
  simp

/-- Four linear coordinate laws give compatibility around a square with
different changes of coordinates on its two restriction maps. -/
lemma linearChange_pullback_comparison_twistedSquare
    {K R : Type u} [CommRing K] [CommRing R] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of K)) (q : Y ⟶ Spec (CommRingCat.of R))
    {L : LineBundle X} {M : LineBundle Y} {n : ℕ}
    (s : Fin (n + 1) → GlobalSections L.obj)
    (t : Fin (n + 1) → GlobalSections M.obj)
    (hs : (⨆ i, trivializationOpen L.obj (s i)) = ⊤)
    (r d : Y ⟶ X) (a : Y ⟶ Y) (b : X ⟶ X)
    (w : r ≫ b = a ≫ d) (φ : K →+* R)
    (hr : q ≫ Spec.map (CommRingCat.ofHom φ) = r ≫ p) (ha : a ≫ q = q)
    (δ : (Scheme.Modules.pullback d).obj L.obj ⟶ M.obj)
    (α : (Scheme.Modules.pullback r).obj L.obj ⟶ M.obj)
    (β : (Scheme.Modules.pullback b).obj L.obj ⟶ L.obj)
    (γ : (Scheme.Modules.pullback a).obj M.obj ⟶ M.obj)
    (er ed ea eb' : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R))
    (eb : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (hcoeff : ∀ i j, φ (eb (Pi.single j 1) i) = eb' (Pi.single j 1) i)
    (he : er.trans eb' = ea.trans ed)
    (hδ : ∀ i, δ.app ⊤ (pullbackSection d L.obj (s i)) =
      linearChangeSections q t ed.toLinearMap i)
    (hα : ∀ i, α.app ⊤ (pullbackSection r L.obj (s i)) =
      linearChangeSections q t er.toLinearMap i)
    (hβ : ∀ i, β.app ⊤ (pullbackSection b L.obj (s i)) =
      linearChangeSections p s eb.toLinearMap i)
    (hγ : ∀ i, γ.app ⊤ (pullbackSection a M.obj (t i)) =
      linearChangeSections q t ea.toLinearMap i) :
    PullbackSquareCompatible d r a b w δ α β γ := by
  apply pullback_comparison_square_between L.property s hs d r a b w δ α β γ
  intro i
  rw [hβ, hδ]
  rw [pullback_comparison_linearChange_baseChange (L := L) (M := M)
    p q s (linearChangeSections q t er.toLinearMap) r φ hr α hα
    eb.toLinearMap eb'.toLinearMap hcoeff]
  rw [pullback_comparison_linearChange (L := M) (M := M)
    q t (linearChangeSections q t ea.toLinearMap) a ha γ hγ]
  rw [linearChangeSections_comp, linearChangeSections_comp]
  exact congrArg (fun e => linearChangeSections q t e.toLinearMap i) he

/-- Bundled transition-coordinate data give the square law for actual action comparisons. -/
lemma relativeAction_twistedSquare_of_coordinateData
    {K R : Type u} [CommRing K] [CommRing R] {S T : Scheme.{u}} {n : ℕ}
    (p : S ⟶ Spec (CommRingCat.of K)) (q : T ⟶ Spec (CommRingCat.of R))
    (r d : RelativeProjectiveSpace T n ⟶ RelativeProjectiveSpace S n)
    (er ed ea eb' : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R))
    (eb : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K))
    (w : r ≫ linearAction p eb = linearAction q ea ≫ d)
    (φ : K →+* R)
    (hr : (RelativeProjectiveSpace.toBase T n ≫ q) ≫
        Spec.map (CommRingCat.ofHom φ) =
      r ≫ (RelativeProjectiveSpace.toBase S n ≫ p))
    (hcoeff : ∀ i j, φ (eb (Pi.single j 1) i) = eb' (Pi.single j 1) i)
    (he : er.trans eb' = ea.trans ed)
    (δ : { e : (Scheme.Modules.pullback d).obj
        (RelativeProjectiveSpace.twistOne S n).obj ≅
          (RelativeProjectiveSpace.twistOne T n).obj //
      ∀ i, e.hom.app ⊤ (pullbackSection d (RelativeProjectiveSpace.twistOne S n).obj
        (RelativeProjectiveSpace.twistOneCoordinate S n i)) =
          changedRelativeProjectiveCoordinates q ed i })
    (α : { e : (Scheme.Modules.pullback r).obj
        (RelativeProjectiveSpace.twistOne S n).obj ≅
          (RelativeProjectiveSpace.twistOne T n).obj //
      ∀ i, e.hom.app ⊤ (pullbackSection r (RelativeProjectiveSpace.twistOne S n).obj
        (RelativeProjectiveSpace.twistOneCoordinate S n i)) =
          changedRelativeProjectiveCoordinates q er i }) :
    PullbackSquareCompatible d r (linearAction q ea) (linearAction p eb) w
      δ.val.hom α.val.hom (relativeLinearActionTwistIso p eb).hom
        (relativeLinearActionTwistIso q ea).hom := by
  exact linearChange_pullback_comparison_twistedSquare
    (L := RelativeProjectiveSpace.twistOne S n)
    (M := RelativeProjectiveSpace.twistOne T n)
    (RelativeProjectiveSpace.toBase S n ≫ p)
    (RelativeProjectiveSpace.toBase T n ≫ q)
    (RelativeProjectiveSpace.twistOneCoordinate S n)
    (RelativeProjectiveSpace.twistOneCoordinate T n)
    (isOpenCover_trivializationOpen (L := RelativeProjectiveSpace.twistOne S n)
      (relativeProjectiveCoordinates_generate S n))
    r d (linearAction q ea) (linearAction p eb) w φ hr
    (by simp only [linearAction_toBase_assoc])
    δ.val.hom α.val.hom (relativeLinearActionTwistIso p eb).hom
    (relativeLinearActionTwistIso q ea).hom er ed ea eb' eb hcoeff he
    δ.property α.property
    (relativeLinearActionTwistIso_coordinate p eb)
    (relativeLinearActionTwistIso_coordinate q ea)

end Langlands.AlgebraicGeometry.LinearSystem

namespace Langlands.Scheme.Modules.RefinedPullbackComparison

/-- A chart normalization and its outer composition give the canonical square map. -/
lemma comp_normalize_eq_square {X Y U P : Scheme.{u}}
    (E : X ⟶ Y) (j : U ⟶ X) (a : U ⟶ P) (k : P ⟶ Y)
    (h : a ≫ k = j ≫ E) (G : Y.Modules) {L : P.Modules}
    (e : (Scheme.Modules.pullback k).obj G ≅ L) :
    compHom j E (j ≫ E) rfl G ≫ (normalize a k (j ≫ E) h e).hom =
      (squarePullbackIso k j a E h.symm G).hom ≫ (Scheme.Modules.pullback a).map e.hom := by
  rw [← CommonSourceCocycle.square_normalize k j a E h.symm G (j ≫ E) h]
  simp [normalize]

/-- Normalized chart comparisons preserve restriction with arbitrary local targets. -/
lemma normalize_local_restrict_between {X Y U V PU PV : Scheme.{u}}
    (E : X ⟶ Y) (aU : U ⟶ X) (aV : V ⟶ X) (t : U ⟶ V)
    (hta : t ≫ aV = aU)
    (r : U ⟶ PU) (q : V ⟶ PV) (c : PU ⟶ PV)
    (cU : PU ⟶ Y) (cV : PV ⟶ Y)
    (ht : r ≫ c = t ≫ q) (hU : r ≫ cU = aU ≫ E)
    (hV : q ≫ cV = aV ≫ E) (hc : c ≫ cV = cU)
    (G : Y.Modules) {LU : U.Modules} {LV : V.Modules}
    {MU : PU.Modules} {MV : PV.Modules}
    (eU : (Scheme.Modules.pullback cU).obj G ≅ MU)
    (eV : (Scheme.Modules.pullback cV).obj G ≅ MV)
    (β : (Scheme.Modules.pullback c).obj MV ≅ MU)
    (he : (Scheme.Modules.pullback c).map eV.hom ≫ β.hom =
      compHom c cV cU hc G ≫ eU.hom)
    (αU : (Scheme.Modules.pullback r).obj MU ⟶ LU)
    (αV : (Scheme.Modules.pullback q).obj MV ⟶ LV)
    (γ : (Scheme.Modules.pullback t).obj LV ⟶ LU)
    (hα : Langlands.AlgebraicGeometry.LinearSystem.PullbackSquareCompatible
      q r t c ht αV αU β.hom γ) :
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

end Langlands.Scheme.Modules.RefinedPullbackComparison

namespace Langlands.AlgebraicGeometry.ProjectiveBundle.FrameAtlas

open Langlands.AlgebraicGeometry.LinearSystem

variable {S : Scheme.{u}} {M : S.Modules} {n : ℕ}
    (a : FrameAtlas M n) (hM : IsLocallyFreeOfRank M (n + 1))

/-- The actual atlas restrictions intertwine the changes to the fixed frames. -/
lemma comparisonCoordinate_square {U V : a.openCover.I₀} (h : U ⟶ V) :
    a.cocycle.chartFunctor.map h ≫ globalLinearAction n (a.comparisonCoordinate V) =
      globalLinearAction n (a.comparisonCoordinate U) ≫
        FrameBundle.chartMap hM
          (show a.toFrameOpen U ≤ a.toFrameOpen V from leOfHom h) := by
  change (globalLinearAction n (a.cocycle.transition h) ≫
      RelativeProjectiveSpace.map n (a.openCover.trans h)) ≫ _ = _
  rw [Category.assoc, map_globalLinearAction, ← Category.assoc,
    globalLinearAction_comp, a.comparisonCoordinate_compatible hM h,
    ← globalLinearAction_comp]
  simp only [Category.assoc]
  rw [a.openCover_trans]
  rfl

/-- Coordinate laws determine the square of frame-atlas comparisons. -/
lemma chartTwist_comparison_criterion {U V : a.openCover.I₀} (h : U ⟶ V)
    (δ : (Scheme.Modules.pullback (FrameBundle.chartMap hM
        (show a.toFrameOpen U ≤ a.toFrameOpen V from leOfHom h))).obj
      (RelativeProjectiveSpace.twistOne V.val.toScheme n).obj ⟶
        (RelativeProjectiveSpace.twistOne U.val.toScheme n).obj)
    (α : (Scheme.Modules.pullback (a.cocycle.chartFunctor.map h)).obj
      (RelativeProjectiveSpace.twistOne V.val.toScheme n).obj ⟶
        (RelativeProjectiveSpace.twistOne U.val.toScheme n).obj)
    (β : (Scheme.Modules.pullback (globalLinearAction n (a.comparisonCoordinate V))).obj
      (RelativeProjectiveSpace.twistOne V.val.toScheme n).obj ⟶
        (RelativeProjectiveSpace.twistOne V.val.toScheme n).obj)
    (γ : (Scheme.Modules.pullback (globalLinearAction n (a.comparisonCoordinate U))).obj
      (RelativeProjectiveSpace.twistOne U.val.toScheme n).obj ⟶
        (RelativeProjectiveSpace.twistOne U.val.toScheme n).obj)
    (hδ : ∀ i, δ.app ⊤ (pullbackSection (FrameBundle.chartMap hM
        (show a.toFrameOpen U ≤ a.toFrameOpen V from leOfHom h))
      (RelativeProjectiveSpace.twistOne V.val.toScheme n).obj
      (RelativeProjectiveSpace.twistOneCoordinate V.val.toScheme n i)) =
      changedRelativeProjectiveCoordinates U.val.toScheme.toSpecΓ
        ((frameCocycle M n hM).transition
          (homOfLE (show a.toFrameOpen U ≤ a.toFrameOpen V from leOfHom h))) i)
    (hα : ∀ i, α.app ⊤ (pullbackSection (a.cocycle.chartFunctor.map h)
      (RelativeProjectiveSpace.twistOne V.val.toScheme n).obj
      (RelativeProjectiveSpace.twistOneCoordinate V.val.toScheme n i)) =
      changedRelativeProjectiveCoordinates U.val.toScheme.toSpecΓ (a.cocycle.transition h) i)
    (hβ : ∀ i, β.app ⊤
      (pullbackSection (globalLinearAction n (a.comparisonCoordinate V))
        (RelativeProjectiveSpace.twistOne V.val.toScheme n).obj
        (RelativeProjectiveSpace.twistOneCoordinate V.val.toScheme n i)) =
      changedRelativeProjectiveCoordinates V.val.toScheme.toSpecΓ (a.comparisonCoordinate V) i)
    (hγ : ∀ i, γ.app ⊤
      (pullbackSection (globalLinearAction n (a.comparisonCoordinate U))
        (RelativeProjectiveSpace.twistOne U.val.toScheme n).obj
        (RelativeProjectiveSpace.twistOneCoordinate U.val.toScheme n i)) =
      changedRelativeProjectiveCoordinates U.val.toScheme.toSpecΓ (a.comparisonCoordinate U) i) :
    PullbackSquareCompatible
      (FrameBundle.chartMap hM
        (show a.toFrameOpen U ≤ a.toFrameOpen V from leOfHom h))
      (a.cocycle.chartFunctor.map h)
      (globalLinearAction n (a.comparisonCoordinate U))
      (globalLinearAction n (a.comparisonCoordinate V))
      (a.comparisonCoordinate_square hM h) δ α β γ := by
  exact linearChange_pullback_comparison_twistedSquare
    (L := RelativeProjectiveSpace.twistOne V.val.toScheme n)
    (M := RelativeProjectiveSpace.twistOne U.val.toScheme n)
    (RelativeProjectiveSpace.toBase V.val.toScheme n ≫ V.val.toScheme.toSpecΓ)
    (RelativeProjectiveSpace.toBase U.val.toScheme n ≫ U.val.toScheme.toSpecΓ)
    (RelativeProjectiveSpace.twistOneCoordinate V.val.toScheme n)
    (RelativeProjectiveSpace.twistOneCoordinate U.val.toScheme n)
    (isOpenCover_trivializationOpen
      (L := RelativeProjectiveSpace.twistOne V.val.toScheme n)
      (relativeProjectiveCoordinates_generate V.val.toScheme n))
    (a.cocycle.chartFunctor.map h)
    (FrameBundle.chartMap hM
      (show a.toFrameOpen U ≤ a.toFrameOpen V from leOfHom h))
    (globalLinearAction n (a.comparisonCoordinate U))
    (globalLinearAction n (a.comparisonCoordinate V))
    (a.comparisonCoordinate_square hM h) (a.openCover.trans h).appTop.hom
    (a.cocycle.chartMap_toSpecΓ h) (by simp only [globalLinearAction_toBase_assoc])
    δ α β γ
    (a.cocycle.transition h)
    ((frameCocycle M n hM).transition
      (homOfLE (show a.toFrameOpen U ≤ a.toFrameOpen V from leOfHom h)))
    (a.comparisonCoordinate U)
    (coordinatePullback n (a.openCover.trans h) (a.comparisonCoordinate V))
    (a.comparisonCoordinate V)
    (fun i j => (coordinatePullback_coeff n (a.openCover.trans h)
      (a.comparisonCoordinate V) i j).symm)
    (a.comparisonCoordinate_compatible hM h)
    hδ hα hβ hγ

/-- The actual four degree-one comparisons satisfy the restriction square. -/
lemma chartTwistIso_comparison_square {U V : a.openCover.I₀} (h : U ⟶ V) :
    PullbackSquareCompatible
      (FrameBundle.chartMap hM
        (show a.toFrameOpen U ≤ a.toFrameOpen V from leOfHom h))
      (a.cocycle.chartFunctor.map h)
      (globalLinearAction n (a.comparisonCoordinate U))
      (globalLinearAction n (a.comparisonCoordinate V))
      (a.comparisonCoordinate_square hM h)
      (FrameBundle.chartTwistIso hM
        (show a.toFrameOpen U ≤ a.toFrameOpen V from leOfHom h)).hom
      (a.cocycle.chartTwistIso h).hom
      (globalLinearActionTwistIso V.val.toScheme n (a.comparisonCoordinate V)).hom
      (globalLinearActionTwistIso U.val.toScheme n (a.comparisonCoordinate U)).hom :=
  relativeAction_twistedSquare_of_coordinateData
    V.val.toScheme.toSpecΓ U.val.toScheme.toSpecΓ
    (a.cocycle.chartFunctor.map h)
    (FrameBundle.chartMap hM
      (show a.toFrameOpen U ≤ a.toFrameOpen V from leOfHom h))
    (a.cocycle.transition h)
    ((frameCocycle M n hM).transition
      (homOfLE (show a.toFrameOpen U ≤ a.toFrameOpen V from leOfHom h)))
    (a.comparisonCoordinate U)
    (coordinatePullback n (a.openCover.trans h) (a.comparisonCoordinate V))
    (a.comparisonCoordinate V)
    (a.comparisonCoordinate_square hM h) (a.openCover.trans h).appTop.hom
    (a.cocycle.chartMap_toSpecΓ h)
    (fun i j => (coordinatePullback_coeff n (a.openCover.trans h)
      (a.comparisonCoordinate V) i j).symm)
    (a.comparisonCoordinate_compatible hM h)
    ((frameCocycle M n hM).chartTwistData
      (homOfLE (show a.toFrameOpen U ≤ a.toFrameOpen V from leOfHom h)))
    (a.cocycle.chartTwistData h)

/-- Express the existing chart isomorphism by canonical normalization. -/
lemma twistChartIso_hom_normalize (U : a.opens) :
    (a.twistChartIso hM U).hom =
      compHom (a.cocycle.chart U) (a.toFrameBundleIso hM).hom
        (a.cocycle.chart U ≫ (a.toFrameBundleIso hM).hom) rfl
        (FrameBundle.twistOne hM).obj ≫
      (RefinedPullbackComparison.normalize (globalLinearAction n (a.comparisonCoordinate U))
        (FrameBundle.chart hM (a.toFrameOpen U))
        (a.cocycle.chart U ≫ (a.toFrameBundleIso hM).hom)
        (a.chart_toFrameBundleIso_hom hM U).symm
        (FrameBundle.twistOneModuleIso hM (a.toFrameOpen U))).hom ≫
      (globalLinearActionTwistIso U.val.toScheme n (a.comparisonCoordinate U)).hom := by
  rw [reassoc_of% (RefinedPullbackComparison.comp_normalize_eq_square
    (a.toFrameBundleIso hM).hom (a.cocycle.chart U)
    (globalLinearAction n (a.comparisonCoordinate U))
    (FrameBundle.chart hM (a.toFrameOpen U))
    (a.chart_toFrameBundleIso_hom hM U).symm
    (FrameBundle.twistOne hM).obj
    (FrameBundle.twistOneModuleIso hM (a.toFrameOpen U)))]
  rfl

/-- The existing chart isomorphisms commute with every frame-atlas restriction. -/
lemma twistChartIso_restrict {U V : a.openCover.I₀} (h : U ⟶ V) :
    (Scheme.Modules.pullback (a.cocycle.chartFunctor.map h)).map
        (a.twistChartIso hM V).hom ≫ (a.cocycle.chartTwistIso h).hom =
      compHom (a.cocycle.chartFunctor.map h) (a.cocycle.chart V) (a.cocycle.chart U)
        (a.cocycle.transition_chart h) (a.twistOne hM).obj ≫
          (a.twistChartIso hM U).hom := by
  rw [a.twistChartIso_hom_normalize hM V, a.twistChartIso_hom_normalize hM U]
  exact RefinedPullbackComparison.normalize_local_restrict_between
    (a.toFrameBundleIso hM).hom (a.cocycle.chart U) (a.cocycle.chart V)
    (a.cocycle.chartFunctor.map h) (a.cocycle.transition_chart h)
    (globalLinearAction n (a.comparisonCoordinate U))
    (globalLinearAction n (a.comparisonCoordinate V))
    (FrameBundle.chartMap hM
      (show a.toFrameOpen U ≤ a.toFrameOpen V from leOfHom h))
    (FrameBundle.chart hM (a.toFrameOpen U)) (FrameBundle.chart hM (a.toFrameOpen V))
    (a.comparisonCoordinate_square hM h).symm
    (a.chart_toFrameBundleIso_hom hM U).symm
    (a.chart_toFrameBundleIso_hom hM V).symm
    (FrameBundle.chartMap_chart hM
      (show a.toFrameOpen U ≤ a.toFrameOpen V from leOfHom h))
    (FrameBundle.twistOne hM).obj
    (FrameBundle.twistOneModuleIso hM (a.toFrameOpen U))
    (FrameBundle.twistOneModuleIso hM (a.toFrameOpen V))
    (FrameBundle.chartTwistIso hM
      (show a.toFrameOpen U ≤ a.toFrameOpen V from leOfHom h))
    (FrameBundle.twistOneModuleIso_restrict hM
      (show a.toFrameOpen U ≤ a.toFrameOpen V from leOfHom h))
    (globalLinearActionTwistIso U.val.toScheme n (a.comparisonCoordinate U)).hom
    (globalLinearActionTwistIso V.val.toScheme n (a.comparisonCoordinate V)).hom
    (a.cocycle.chartTwistIso h).hom
    (a.chartTwistIso_comparison_square hM h).reverse

/-- The existing larger chart comparison followed by the full atlas restriction. -/
def twistRestrictionIso {U V : a.openCover.I₀} (h : U ⟶ V) :
    (Scheme.Modules.pullback (a.cocycle.chartFunctor.map h)).obj
      ((Scheme.Modules.pullback (a.cocycle.chart V)).obj (a.twistOne hM).obj) ≅
        (RelativeProjectiveSpace.twistOne U.val.toScheme n).obj :=
  (Scheme.Modules.pullback (a.cocycle.chartFunctor.map h)).mapIso (a.twistChartIso hM V) ≪≫
    a.cocycle.chartTwistIso h

/-- The nested chart comparison is canonical composition followed by the smaller chart. -/
lemma twistRestrictionIso_hom {U V : a.openCover.I₀} (h : U ⟶ V) :
    (a.twistRestrictionIso hM h).hom =
      compHom (a.cocycle.chartFunctor.map h) (a.cocycle.chart V) (a.cocycle.chart U)
        (a.cocycle.transition_chart h) (a.twistOne hM).obj ≫
          (a.twistChartIso hM U).hom :=
  a.twistChartIso_restrict hM h

end Langlands.AlgebraicGeometry.ProjectiveBundle.FrameAtlas
