import Langlands.Geometry.Analytic.FullRecognitionPairComposition
import Langlands.Geometry.Analytic.FieldPointCommonChartTests
import Langlands.Geometry.Analytic.QuasiEtaleRigidity.ChartCoverRigidity
import Langlands.Geometry.Analytic.UnramifiedAgreementNeighborhood

/-! # Chartwise agreement over finite unramified pieces -/

noncomputable section

universe u v uL

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set Filter Topology PresentedAffinoidAlgebra AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem domainInclusion_comp_eq_of_pullback_eq
    {T P : SaturatedAtlasPresentation.{u, v, v} K} (a b : T ⟶ P)
    (i : T.presentation.atlas.Index) (j : P.presentation.atlas.Index)
    (ha : a.baseMap '' range (T.presentation.atlas.chart i) ⊆ range (P.presentation.atlas.chart j))
    (hb : b.baseMap '' range (T.presentation.atlas.chart i) ⊆ range (P.presentation.atlas.chart j))
    (heq : a.pullback i j ha = b.pullback i j hb) :
    T.domainInclusion (T.chartDomain i) ≫ a = T.domainInclusion (T.chartDomain i) ≫ b := by
  let D := T.chartDomain i
  let t : (T.domain D).presentation.atlas.Index := ⟨i, Subset.rfl⟩
  have ht : range ((T.domain D).presentation.atlas.chart t) = univ := by
    exact (T.presentation.atlas.range_subspaceChart D.carrier
      (show T.presentation.atlas.SubspaceChart D.carrier from t)).trans
      (eq_univ_of_forall fun x => x.property)
  have ha' : (T.domainInclusion D ≫ a).baseMap ''
      range ((T.domain D).presentation.atlas.chart t) ⊆ range (P.presentation.atlas.chart j) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ha ⟨_, mem_range_self x, rfl⟩
  have hb' : (T.domainInclusion D ≫ b).baseMap ''
      range ((T.domain D).presentation.atlas.chart t) ⊆ range (P.presentation.atlas.chart j) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact hb ⟨_, mem_range_self x, rfl⟩
  apply StrongHom.eq_of_global_pullback_eq (T.domain D).hasAllLocalDomains t ht _ _ j ha' hb'
  rw [domainInclusion_comp_pullback a D t j ha ha', domainInclusion_comp_pullback b D t j hb hb']
  exact heq

/-- Shrinking around a spectrum point transfers bounded agreement to an
actual chart inclusion. Its new chart range contains a relative neighbourhood. -/
theorem exists_chart_eq_of_agreementNeighborhood
    {T P : SaturatedAtlasPresentation.{u, v, v} K} (a b : T ⟶ P)
    (i : T.presentation.atlas.Index) (j : P.presentation.atlas.Index)
    (ha : a.baseMap '' range (T.presentation.atlas.chart i) ⊆ range (P.presentation.atlas.chart j))
    (hb : b.baseMap '' range (T.presentation.atlas.chart i) ⊆ range (P.presentation.atlas.chart j))
    (x : BanachSpectrum (T.presentation.atlas.algebra i))
    (N : BoundedAlgHom.AgreementNeighborhood (a.pullback i j ha) (b.pullback i j hb) x) :
    ∃ k : T.presentation.atlas.Index,
      range (T.presentation.atlas.chart k) ⊆ range (T.presentation.atlas.chart i) ∧
      range (T.presentation.atlas.chart k) ∈ 𝓝[range (T.presentation.atlas.chart i)]
        (T.presentation.atlas.chart i x) ∧
      T.domainInclusion (T.chartDomain k) ≫ a = T.domainInclusion (T.chartDomain k) ≫ b := by
  let t := T.presentation.atlas
  obtain ⟨d, hd, hdN⟩ := RationalChart.exists_rational_neighborhood x N.carrier
    (N.isOpen.mem_nhds N.mem)
  obtain ⟨k, hk⟩ := T.hasAllLocalDomains.exists_chart (⟨i, d.toDomain⟩ : IndexedAffinoidAtlas.LocalDomain t)
  change range (t.chart k) = t.chart i '' d.locus at hk
  have hki : range (t.chart k) ⊆ range (t.chart i) := by
    rw [hk]
    rintro _ ⟨y, _, rfl⟩
    exact mem_range_self y
  have hres : ∀ y, BanachSpectrum.comap (t.restriction k i hki).toBoundedRingHom y ∈ N.carrier := by
    intro y
    have hm := mem_range_self (f := t.chart k) y
    rw [hk] at hm
    obtain ⟨z, hz, hzy⟩ := hm
    have he : BanachSpectrum.comap (t.restriction k i hki).toBoundedRingHom y = z :=
      (t.isEmbedding_chart i).injective ((t.restriction_chart k i hki y).trans hzy.symm)
    rw [he]
    exact hdN hz
  refine ⟨k, hki, ?_, domainInclusion_comp_eq_of_pullback_eq a b k j
    ((image_mono hki).trans ha) ((image_mono hki).trans hb) ?_⟩
  · rw [(t.isEmbedding_chart i).nhds_eq_comap, Filter.mem_comap] at hd
    obtain ⟨O, hO, hOd⟩ := hd
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨O, hO, ?_⟩
    rintro _ ⟨hyO, y, rfl⟩
    rw [hk]
    exact ⟨y, hOd hyO, rfl⟩
  · rw [← a.restriction_comp_pullback k i j hki _ ha,
      ← b.restriction_comp_pullback k i j hki _ hb]
    exact N.comp_eq _ _ hres

set_option linter.defProp false in
/-- Two strong maps with a common composite and the same full field point
agree on a smaller chart whenever they land in the same finite unramified piece. -/
def exists_chart_eq_over_unramifiedPiece
    {T A B : AffinoidAtlasPresentation.{u, v, v} K}
    {L : Type uL} [NormedField L] [NormedAlgebra K L]
    (a b : ofSaturation T ⟶ ofSaturation A) (f : ofSaturation A ⟶ ofSaturation B)
    (hab : a ≫ f = b ≫ f) (q : FieldPoint L (ofSaturation T).presentation)
    (hq : q.map a (ofSaturation T).hasAllLocalDomains =
      q.map b (ofSaturation T).hasAllLocalDomains)
    (i : T.atlas.saturatedAtlas.Index) (hi : q.point ∈ range (T.atlas.saturatedAtlas.chart i))
    (V : A.atlas.saturatedAtlas.RecognizedSubset) (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (hV : f.baseMap '' range V.chart ⊆ range W.chart)
    (hfin : (f.fullRecognitionPairs.pullback V W hV).IsFiniteBanach)
    (hu : ∀ p : BanachSpectrum V.algebra, V.chart p = a.baseMap q.point →
      (f.fullRecognitionPairs.pullback V W hV).IsUnramifiedAtPoint p)
    (ha : a.baseMap '' range (T.atlas.saturatedAtlas.chart i) ⊆ range V.chart)
    (hb : b.baseMap '' range (T.atlas.saturatedAtlas.chart i) ⊆ range V.chart) :
    ∃ k : T.atlas.saturatedAtlas.Index,
      range (T.atlas.saturatedAtlas.chart k) ⊆ range (T.atlas.saturatedAtlas.chart i) ∧
      range (T.atlas.saturatedAtlas.chart k) ∈ 𝓝[range (T.atlas.saturatedAtlas.chart i)] q.point ∧
      (ofSaturation T).domainInclusion ((ofSaturation T).chartDomain k) ≫ a =
        (ofSaturation T).domainInclusion ((ofSaturation T).chartDomain k) ≫ b := by
  let E := ofSaturation T
  let F := ofFullRecognition A
  let η : ofSaturation A ⟶ F := A.localDomainToFullRecognition
  let a' : E ⟶ F := a ≫ η
  let b' : E ⟶ F := b ≫ η
  have ha' : a'.baseMap '' range (E.presentation.atlas.chart i) ⊆
      range (F.presentation.atlas.chart V) := ha
  have hb' : b'.baseMap '' range (E.presentation.atlas.chart i) ⊆
      range (F.presentation.atlas.chart V) := hb
  have haW : (a ≫ f).toFullRecognitionTarget.baseMap '' range (T.atlas.saturatedAtlas.chart i) ⊆
      range (B.fullRecognitionPresentation.atlas.chart W) := by
    rintro _ ⟨p, hp, rfl⟩
    exact hV ⟨a.baseMap p, ha ⟨p, hp, rfl⟩, rfl⟩
  have hbW : (b ≫ f).toFullRecognitionTarget.baseMap '' range (T.atlas.saturatedAtlas.chart i) ⊆
      range (B.fullRecognitionPresentation.atlas.chart W) := by
    rintro _ ⟨p, hp, rfl⟩
    exact hV ⟨b.baseMap p, hb ⟨p, hp, rfl⟩, rfl⟩
  let f₀ := f.fullRecognitionPairs.pullback V W hV
  have hbase : (a'.pullback i V ha').comp f₀ = (b'.pullback i V hb').comp f₀ := by
    have ha₀ := StrongHom.toFullRecognitionTarget_pullback_comp_fullRecognitionPairs a f i V W ha' hV haW
    have hb₀ := StrongHom.toFullRecognitionTarget_pullback_comp_fullRecognitionPairs b f i V W hb' hV hbW
    have h : (show E ⟶ ofFullRecognition B from (a ≫ f).toFullRecognitionTarget) =
        (show E ⟶ ofFullRecognition B from (b ≫ f).toFullRecognitionTarget) :=
      congrArg (fun g : E ⟶ ofSaturation B => g.toFullRecognitionTarget) hab
    exact ha₀.trans ((pullback_congr h i W haW hbW).trans hb₀.symm)
  have hq' : q.map a' E.hasAllLocalDomains = q.map b' E.hasAllLocalDomains := by
    change q.map (a.saturatedComp η _ _) _ = q.map (b.saturatedComp η _ _) _
    rw [FieldPoint.map_saturatedComp, FieldPoint.map_saturatedComp, hq]
  obtain ⟨x, hx, hnorm⟩ := q.isChartPoint i hi
  have he : ∀ z, x (a'.pullback i V ha' z - b'.pullback i V hb' z) = 0 := by
    intro z
    have hqa := ha' ⟨q.point, hi, rfl⟩
    have hqb := hb' ⟨q.point, hi, rfl⟩
    have h := (q.map_eval a' E.hasAllLocalDomains V hqa i hi ha').symm.trans
      ((FieldPoint.eval_congr hq' V hqa hqb).trans (q.map_eval b' E.hasAllLocalDomains V hqb i hi hb'))
    have hz : q.eval i hi (a'.pullback i V ha' z) = q.eval i hi (b'.pullback i V hb' z) :=
      congrArg (fun φ : V.algebra →ₐ[K] L => φ z) h
    calc
      _ = ‖q.eval i hi (a'.pullback i V ha' z - b'.pullback i V hb' z)‖ := (hnorm _).symm
      _ = 0 := by rw [map_sub, hz, sub_self, norm_zero]
  have hpoint : V.chart (BanachSpectrum.comap (a'.pullback i V ha').toBoundedRingHom x) =
      a.baseMap q.point := (a'.chart_comm i V ha' x).trans (congrArg a.baseMap hx)
  let H := f₀.unramifiedAgreementNeighborhood hfin.finite.finiteType _ _ hbase x he (hu _ hpoint)
  obtain ⟨k, hki, hk, heq⟩ := exists_chart_eq_of_agreementNeighborhood a' b' i V ha' hb' x H
  refine ⟨k, hki, hx ▸ hk, ?_⟩
  apply (postcompQuasiIsoEmbedding η A.localDomainToFullRecognition_isQuasiIso).injective
  let j := E.domainInclusion (E.chartDomain k)
  change (j ≫ a) ≫ η = (j ≫ b) ≫ η
  exact (Category.assoc j a η).trans (heq.trans (Category.assoc j b η).symm)

end Langlands.Analytic.SaturatedAtlasPresentation
