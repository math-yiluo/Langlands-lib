import Langlands.Geometry.Analytic.FullRecognitionPairSystems
import Langlands.Geometry.Analytic.AtlasTopology.DomainIntersections

/-! # Berkovich's local condition for full-recognition pair systems -/

noncomputable section

universe u v w v' w'

namespace Langlands.Analytic

open CategoryTheory Set Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation

namespace AdmissiblePairSystem

variable {A : AffinoidAtlasPresentation.{u, v, w} K} {B : AffinoidAtlasPresentation.{u, v', w'} K}

/-- Berkovich's local condition: every point has finitely many admissible
chart pairs whose source charts all contain the point, with source union a
neighborhood of the point and target union a neighborhood of its image. -/
def LocalCondition (p : AdmissiblePairSystem A B) : Prop :=
  ∀ x : A.space, ∃ I : Set (A.atlas.Index × B.atlas.Index), I.Finite ∧
    (∀ q ∈ I, x ∈ Set.range (A.atlas.chart q.1)) ∧
    (∀ q ∈ I, p.baseMap '' Set.range (A.atlas.chart q.1) ⊆ Set.range (B.atlas.chart q.2)) ∧
    (⋃ q ∈ I, Set.range (A.atlas.chart q.1)) ∈ 𝓝 x ∧
    (⋃ q ∈ I, Set.range (B.atlas.chart q.2)) ∈ 𝓝 (p.baseMap x)

end AdmissiblePairSystem

namespace StrongHom

section ChartLevel

variable {P Q : AffinoidAtlasPresentation.{u, v, w} K} (h : StrongHom P Q)

/-- If the source atlas contains all local domains, the part of a source chart
mapping into a target chart inside an admissible target is a source chart. -/
theorem exists_chart_inter_preimage (hP : P.atlas.HasAllLocalDomains) (k : P.atlas.Index)
    (j l : Q.atlas.Index)
    (hkj : h.baseMap '' Set.range (P.atlas.chart k) ⊆ Set.range (Q.atlas.chart j))
    (hlj : Set.range (Q.atlas.chart l) ⊆ Set.range (Q.atlas.chart j)) :
    ∃ i : P.atlas.Index, Set.range (P.atlas.chart i) =
      Set.range (P.atlas.chart k) ∩ h.baseMap ⁻¹' Set.range (Q.atlas.chart l) := by
  let U : LocalDomain P.atlas :=
    ⟨k, Domain.pullback (h.pullback k j hkj) (Q.atlas.restrictionDomain l j hlj)⟩
  obtain ⟨i, hi⟩ := hP.exists_chart U
  refine ⟨i, hi.trans ?_⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Set.mem_range_self x, ?_⟩
    have hx' : Q.atlas.chart j (BanachSpectrum.comap (h.pullback k j hkj).toBoundedRingHom x) ∈
        Set.range (Q.atlas.chart l) := hx
    exact (congrArg (fun y => y ∈ Set.range (Q.atlas.chart l)) (h.chart_comm k j hkj x)).mp hx'
  · rintro ⟨⟨x, rfl⟩, hz⟩
    refine ⟨x, ?_, rfl⟩
    change Q.atlas.chart j (BanachSpectrum.comap (h.pullback k j hkj).toBoundedRingHom x) ∈
      Set.range (Q.atlas.chart l)
    exact (congrArg (fun y => y ∈ Set.range (Q.atlas.chart l)) (h.chart_comm k j hkj x)).mpr hz

/-- A strong map whose source atlas contains all local domains satisfies the
local condition already on original charts. -/
theorem localCondition_of_hasAllLocalDomains (hP : P.atlas.HasAllLocalDomains) :
    h.toAdmissiblePairSystem.LocalCondition := by
  classical
  intro x
  change ∃ I : Set (P.atlas.Index × Q.atlas.Index), I.Finite ∧
    (∀ q ∈ I, x ∈ Set.range (P.atlas.chart q.1)) ∧
    (∀ q ∈ I, h.baseMap '' Set.range (P.atlas.chart q.1) ⊆ Set.range (Q.atlas.chart q.2)) ∧
    (⋃ q ∈ I, Set.range (P.atlas.chart q.1)) ∈ 𝓝 x ∧
    (⋃ q ∈ I, Set.range (Q.atlas.chart q.2)) ∈ 𝓝 (h.baseMap x)
  obtain ⟨ρ, hρf, hρsub, hρx, hρn⟩ := P.atlas.isNet_chartFamily.1 x
  obtain ⟨τ, hτf, hτsub, hτy, hτn⟩ := Q.atlas.isNet_chartFamily.1 (h.baseMap x)
  have : Finite ρ := hρf.to_subtype
  have : Finite τ := hτf.to_subtype
  choose sidx hsidx using fun U : ρ => hρsub U.property
  have hs : ∀ U : ρ, Set.range (P.atlas.chart (sidx U)) = U.val := hsidx
  choose tidx htidx using fun V : τ => hτsub V.property
  have ht : ∀ V : τ, Set.range (Q.atlas.chart (tidx V)) = V.val := htidx
  choose T hT using fun U : ρ => h.target_exists (sidx U)
  have hxU : ∀ U : ρ, x ∈ Set.range (P.atlas.chart (sidx U)) := by
    intro U
    rw [hs U]
    exact hρx U.val U.property
  have hyT : ∀ U : ρ, h.baseMap x ∈ Set.range (Q.atlas.chart (T U)) :=
    fun U => hT U ⟨x, hxU U, rfl⟩
  have hloc : ∀ (U : ρ) (V : τ), ∃ σ : Set (Set Q.space), σ.Finite ∧
      σ ⊆ Set.range (fun j => Set.range (Q.atlas.chart j)) ∧
      (∀ W ∈ σ, W ⊆ Set.range (Q.atlas.chart (T U)) ∩ V.val ∧ h.baseMap x ∈ W) ∧
      ⋃₀ σ ∈ 𝓝[Set.range (Q.atlas.chart (T U)) ∩ V.val] (h.baseMap x) := by
    intro U V
    have hnet := Q.atlas.isNet_chartFamily.2 _ (Set.mem_range_self (T U)) _ (hτsub V.property)
    rw [AtlasTopology.isQuasinet_restrictedFamily_iff] at hnet
    exact hnet _ (Set.mem_singleton _) (h.baseMap x) ⟨hyT U, hτy V.val V.property⟩
  choose σ hσf hσsub hσmem hσn using hloc
  have : ∀ (U : ρ) (V : τ), Finite (σ U V) := fun U V => (hσf U V).to_subtype
  choose widx hwidx using fun (U : ρ) (V : τ) (W : σ U V) => hσsub U V W.property
  have hws : ∀ (U : ρ) (V : τ) (W : σ U V),
      Set.range (Q.atlas.chart (widx U V W)) = W.val := hwidx
  have hWT : ∀ (U : ρ) (V : τ) (W : σ U V),
      Set.range (Q.atlas.chart (widx U V W)) ⊆ Set.range (Q.atlas.chart (T U)) :=
    fun U V W => (hws U V W).trans_subset
      ((hσmem U V W.val W.property).1.trans Set.inter_subset_left)
  choose piece hpiece using fun (U : ρ) (V : τ) (W : σ U V) =>
    h.exists_chart_inter_preimage hP (sidx U) (T U) (widx U V W) (hT U) (hWT U V W)
  let F : (Σ U : ρ, Σ V : τ, σ U V) → P.atlas.Index × Q.atlas.Index :=
    fun s => (piece s.1 s.2.1 s.2.2, tidx s.2.1)
  refine ⟨Set.range F, Set.finite_range F, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨⟨U, V, W⟩, rfl⟩
    change x ∈ Set.range (P.atlas.chart (piece U V W))
    rw [hpiece U V W, hws U V W]
    exact ⟨hxU U, (hσmem U V W.val W.property).2⟩
  · rintro _ ⟨⟨U, V, W⟩, rfl⟩
    change h.baseMap '' Set.range (P.atlas.chart (piece U V W)) ⊆
      Set.range (Q.atlas.chart (tidx V))
    rw [hpiece U V W, ht V]
    rintro _ ⟨z, ⟨_, hz⟩, rfl⟩
    have hz' : h.baseMap z ∈ W.val := by
      rw [← hws U V W]
      exact hz
    exact ((hσmem U V W.val W.property).1 hz').2
  · have hO : ∀ (U : ρ) (V : τ), ∃ O ∈ 𝓝 (h.baseMap x),
        O ∩ (Set.range (Q.atlas.chart (T U)) ∩ V.val) ⊆ ⋃₀ σ U V :=
      fun U V => mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (hσn U V)
    choose O hOn hOsub using hO
    have hOall : (⋂ U, ⋂ V, O U V) ∈ 𝓝 (h.baseMap x) :=
      Filter.iInter_mem.2 fun U => Filter.iInter_mem.2 fun V => hOn U V
    have hE : ⋃₀ ρ ∩ h.baseMap ⁻¹' (⋃₀ τ ∩ ⋂ U, ⋂ V, O U V) ∈ 𝓝 x :=
      inter_mem hρn (h.baseMap.continuous.continuousAt.preimage_mem_nhds (inter_mem hτn hOall))
    refine Filter.mem_of_superset hE ?_
    rintro z ⟨⟨U0, hU0, hzU0⟩, ⟨V0, hV0, hzV0⟩, hzO⟩
    let U : ρ := ⟨U0, hU0⟩
    let V : τ := ⟨V0, hV0⟩
    have hzU : z ∈ Set.range (P.atlas.chart (sidx U)) := by
      rw [hs U]
      exact hzU0
    have hzT : h.baseMap z ∈ Set.range (Q.atlas.chart (T U)) := hT U ⟨z, hzU, rfl⟩
    have hzO' : h.baseMap z ∈ O U V := Set.mem_iInter.1 (Set.mem_iInter.1 hzO U) V
    obtain ⟨W0, hW0, hzW0⟩ := hOsub U V ⟨hzO', hzT, hzV0⟩
    let W : σ U V := ⟨W0, hW0⟩
    refine Set.mem_iUnion₂.2 ⟨F ⟨U, V, W⟩, ⟨⟨U, V, W⟩, rfl⟩, ?_⟩
    change z ∈ Set.range (P.atlas.chart (piece U V W))
    rw [hpiece U V W, hws U V W]
    exact ⟨hzU, hzW0⟩
  · obtain ⟨U0, hU0, -⟩ := mem_of_mem_nhds hρn
    refine Filter.mem_of_superset hτn ?_
    rintro y' ⟨V0, hV0, hyV0⟩
    let U : ρ := ⟨U0, hU0⟩
    let V : τ := ⟨V0, hV0⟩
    have hyS : h.baseMap x ∈ Set.range (Q.atlas.chart (T U)) ∩ V.val := ⟨hyT U, hτy V0 hV0⟩
    obtain ⟨W0, hW0, -⟩ := mem_of_mem_nhdsWithin hyS (hσn U V)
    let W : σ U V := ⟨W0, hW0⟩
    refine Set.mem_iUnion₂.2 ⟨F ⟨U, V, W⟩, ⟨⟨U, V, W⟩, rfl⟩, ?_⟩
    change y' ∈ Set.range (Q.atlas.chart (tidx V))
    rw [ht V]
    exact hyV0

end ChartLevel

/-- The pair system on full recognition atlases of a strong map of local-domain
enlargements satisfies Berkovich's local condition, with original local
domains viewed as recognized subsets on both sides. -/
theorem fullRecognitionPairs_localCondition {A B : AffinoidAtlasPresentation.{u, v, w} K}
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation) :
    g.fullRecognitionPairs.LocalCondition := by
  classical
  intro x
  obtain ⟨I, hIf, hIx, hIimg, hIs, hIt⟩ :=
    g.localCondition_of_hasAllLocalDomains A.atlas.saturatedAtlas_hasAllLocalDomains x
  let e : A.atlas.saturatedAtlas.Index × B.atlas.saturatedAtlas.Index →
      A.fullRecognitionPresentation.atlas.Index × B.fullRecognitionPresentation.atlas.Index :=
    fun q => (A.atlas.saturatedAtlas.originalRecognitionIndex q.1,
      B.atlas.saturatedAtlas.originalRecognitionIndex q.2)
  have hsrc : ∀ q, Set.range (A.fullRecognitionPresentation.atlas.chart (e q).1) =
      Set.range (A.atlas.saturatedAtlas.chart q.1) :=
    fun q => A.atlas.saturatedAtlas.recognitionAtlas_original_range q.1
  have htgt : ∀ q, Set.range (B.fullRecognitionPresentation.atlas.chart (e q).2) =
      Set.range (B.atlas.saturatedAtlas.chart q.2) :=
    fun q => B.atlas.saturatedAtlas.recognitionAtlas_original_range q.2
  refine ⟨e '' I, hIf.image e, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact (hsrc q).superset (hIx q hq)
  · rintro _ ⟨q, hq, rfl⟩ _ ⟨z, hz, rfl⟩
    exact (htgt q).superset (hIimg q hq ⟨z, (hsrc q).subset hz, rfl⟩)
  · refine Filter.mem_of_superset hIs ?_
    intro z hz
    obtain ⟨q, hq, hzq⟩ := Set.mem_iUnion₂.1 hz
    exact Set.mem_iUnion₂.2 ⟨e q, ⟨q, hq, rfl⟩, (hsrc q).superset hzq⟩
  · refine Filter.mem_of_superset hIt ?_
    intro z hz
    obtain ⟨q, hq, hzq⟩ := Set.mem_iUnion₂.1 hz
    exact Set.mem_iUnion₂.2 ⟨e q, ⟨q, hq, rfl⟩, (htgt q).superset hzq⟩

end StrongHom

end AffinoidAtlasPresentation

end Langlands.Analytic
