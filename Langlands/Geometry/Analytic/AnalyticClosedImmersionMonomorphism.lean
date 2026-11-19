import Langlands.Geometry.Analytic.AnalyticImmersion
import Langlands.Geometry.Analytic.FibreProductPoints
import Langlands.Geometry.Analytic.LocalDomainSubnetRecognition
import Langlands.Geometry.Analytic.SaturatedLocalizedFractions

/-! # Monicity of analytic closed immersions -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory AffinoidAtlasPresentation IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, v} K} {g : ofSaturation A ⟶ ofSaturation B}

/-- The recognized inverse image of an affinoid domain along a closed strong map,
with its admissible quotient property. -/
def closedImmersionAffinoidPreimage
    (hg : StrongHom.IsClosedImmersion (A := A) (B := B) g)
    (W : B.atlas.saturatedAtlas.RecognizedSubset) :
    {V : A.atlas.saturatedAtlas.RecognizedSubset //
      ∃ (h : g.baseMap '' Set.range V.chart ⊆ Set.range W.chart),
        V.locus = g.baseMap ⁻¹' W.locus ∧
          (g.fullRecognitionPairs.pullback V W h).IsAdmissibleEpi} :=
  ⟨(hg W).choose, (hg W).choose_spec⟩

set_option backward.isDefEq.respectTransparency false in
/-- The surjective bounded quotient maps make the underlying point map injective. -/
theorem injective_of_strongClosedImmersion
    (hg : StrongHom.IsClosedImmersion (A := A) (B := B) g) :
    Function.Injective g.baseMap := by
  intro x y hxy
  obtain ⟨j, hj⟩ := B.atlas.saturatedAtlas.exists_chart_at (g.baseMap x)
  let W := B.atlas.saturatedAtlas.originalRecognitionIndex j
  have hx : g.baseMap x ∈ W.locus :=
    W.range_chart.subset ((B.atlas.saturatedAtlas.recognitionAtlas_original_range j).symm.subset hj)
  obtain ⟨V, h, hV, hep⟩ := closedImmersionAffinoidPreimage hg W
  have hx' : x ∈ Set.range V.chart := by
    rw [V.range_chart, hV]
    exact hx
  have hy' : y ∈ Set.range V.chart := by
    rw [V.range_chart, hV]
    exact (show g.baseMap y ∈ W.locus from hxy ▸ hx)
  obtain ⟨s, rfl⟩ := hx'
  obtain ⟨t, rfl⟩ := hy'
  let q := g.fullRecognitionPairs.pullback V W h
  have hst : BanachSpectrum.comap q.toBoundedRingHom s =
      BanachSpectrum.comap q.toBoundedRingHom t := by
    apply (B.fullRecognitionPresentation.atlas.isEmbedding_chart W).injective
    exact (g.fullRecognitionPairs.chart_comm V W h s).trans
      (hxy.trans (g.fullRecognitionPairs.chart_comm V W h t).symm)
  apply congrArg V.chart
  apply BanachSpectrum.ext
  intro a
  obtain ⟨b, rfl⟩ := hep.1 a
  exact congrArg (fun z : BanachSpectrum W.algebra => z b) hst

set_option backward.isDefEq.respectTransparency false in
private theorem cancel_of_strongClosedImmersion_on_saturation
    (hg : StrongHom.IsClosedImmersion (A := A) (B := B) g)
    {T : AffinoidAtlasPresentation.{u, v, v} K} (a b : ofSaturation T ⟶ ofSaturation A)
    (hab : a ≫ g = b ≫ g) : a = b := by
  have hbase : a.baseMap = b.baseMap := by
    ext x
    exact injective_of_strongClosedImmersion hg
      (congrArg (fun f : ofSaturation T ⟶ ofSaturation B => f.baseMap x) hab)
  apply A.localDomainToFullRecognition_isQuasiIso.cancel_saturatedComp
    T.atlas.saturatedAtlas_hasAllLocalDomains A.atlas.saturatedAtlas_hasAllLocalDomains
  change a.toFullRecognitionTarget = b.toFullRecognitionTarget
  refine StrongHom.ext_of_saturated T.atlas.saturatedAtlas_hasAllLocalDomains hbase ?_
  intro i
  obtain ⟨j, hj⟩ := (a ≫ g).target_exists i
  let W := B.atlas.saturatedAtlas.originalRecognitionIndex j
  have hW : Set.range (B.atlas.saturatedAtlas.chart j) ⊆ Set.range W.chart :=
    (B.atlas.saturatedAtlas.recognitionAtlas_original_range j).symm.subset
  have haW : (a ≫ g).toFullRecognitionTarget.baseMap ''
      Set.range (T.atlas.saturatedAtlas.chart i) ⊆ Set.range W.chart :=
    hj.trans hW
  have hbW : (b ≫ g).toFullRecognitionTarget.baseMap ''
      Set.range (T.atlas.saturatedAtlas.chart i) ⊆ Set.range W.chart := hab ▸ haW
  obtain ⟨V, hVW, hV, hep⟩ := closedImmersionAffinoidPreimage hg W
  have haV : a.toFullRecognitionTarget.baseMap '' Set.range (T.atlas.saturatedAtlas.chart i) ⊆
      Set.range V.chart := by
    rw [V.range_chart, hV]
    rintro _ ⟨x, hx, rfl⟩
    exact W.range_chart.subset (haW ⟨x, hx, rfl⟩)
  have hbV : b.toFullRecognitionTarget.baseMap '' Set.range (T.atlas.saturatedAtlas.chart i) ⊆
      Set.range V.chart := by
    rw [StrongHom.toFullRecognitionTarget_baseMap, ← hbase]
    exact haV
  refine ⟨V, haV, ?_⟩
  have hcomp (f₁ f₂ : ofSaturation T ⟶ ofSaturation B) (e : f₁ = f₂)
      (h₁ : f₁.toFullRecognitionTarget.baseMap '' Set.range (T.atlas.saturatedAtlas.chart i) ⊆
        Set.range W.chart)
      (h₂ : f₂.toFullRecognitionTarget.baseMap '' Set.range (T.atlas.saturatedAtlas.chart i) ⊆
        Set.range W.chart) :
      f₁.toFullRecognitionTarget.pullback i W h₁ =
        f₂.toFullRecognitionTarget.pullback i W h₂ := by
    subst f₂
    rfl
  have he := (a.toFullRecognitionTarget_pullback_comp_fullRecognitionPairs g i V W
      haV hVW haW).trans
    ((hcomp _ _ hab haW hbW).trans
      (b.toFullRecognitionTarget_pullback_comp_fullRecognitionPairs g i V W hbV hVW hbW).symm)
  apply BoundedAlgHom.ext
  intro x
  obtain ⟨t, rfl⟩ := hep.1 x
  exact congrArg (fun q => q t) he

/-- A closed strong map is monic on actual saturated presentations. -/
theorem mono_of_strongClosedImmersion
    (hg : StrongHom.IsClosedImmersion (A := A) (B := B) g) : Mono g where
  right_cancellation {T} a b hab := by
    apply (cancel_epi T.saturationIso.hom).mp
    apply cancel_of_strongClosedImmersion_on_saturation hg
    simp only [Category.assoc, hab]

set_option backward.isDefEq.respectTransparency false in
/-- The localization of a closed strong map is still monic. -/
theorem mono_localizationFunctor_map_of_strongClosedImmersion
    (hg : StrongHom.IsClosedImmersion (A := A) (B := B) g) :
    Mono (localizationFunctor.map g) := by
  let : Mono g := mono_of_strongClosedImmersion hg
  constructor
  intro Z a b hab
  obtain ⟨T, rfl⟩ := localizedObjectEquiv.surjective Z
  obtain ⟨r, rfl⟩ := exists_localizedRightFraction a
  obtain ⟨s, rfl⟩ := exists_localizedRightFraction b
  let post (q : (quasiIsomorphisms (K := K)).RightFraction T (ofSaturation A)) :
      (quasiIsomorphisms (K := K)).RightFraction T (ofSaturation B) :=
    ⟨q.s, q.hs, q.f ≫ g⟩
  have hp (q : (quasiIsomorphisms (K := K)).RightFraction T (ofSaturation A)) :
      localizedRightFraction (post q) = localizedRightFraction q ≫ localizationFunctor.map g := by
    simp only [post, localizedRightFraction, Functor.map_comp, Category.assoc]
  obtain ⟨S, p, q, hd, hn, hs⟩ :=
    (localizedRightFraction_eq_iff (post r) (post s)).mp ((hp r).trans (hab.trans (hp s).symm))
  apply (localizedRightFraction_eq_iff r s).mpr
  exact ⟨S, p, q, hd, (cancel_mono g).mp (by simpa only [post, Category.assoc] using hn), hs⟩

/-- Every analytic closed immersion is a categorical monomorphism. -/
theorem closedImmersion.mono {X Y : LocalizedCategory.{u, v, v} (K := K)} {f : X ⟶ Y}
    (hf : closedImmersion f) : Mono f := by
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := hf
  exact ((MorphismProperty.monomorphisms _).arrow_mk_iso_iff e).mp
    (mono_localizationFunctor_map_of_strongClosedImmersion hg)

end Langlands.Analytic.SaturatedAtlasPresentation
