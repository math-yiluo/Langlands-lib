import Langlands.Geometry.Analytic.FullRecognitionFiniteTargetLocalityStatement
import Langlands.Geometry.Analytic.FiniteOpenAlgebraDescentData
import Langlands.Geometry.Analytic.RecognizedAffinoidNet
import Langlands.Geometry.Analytic.AtlasTopology.DomainIntersections

/-! # Refining a recognized target affinoid by target neighborhood families -/

noncomputable section

universe u v w

open scoped Topology

namespace Langlands.Analytic.IndexedAffinoidAtlas

open Set Filter

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- A contained-chart quasinet of a subspace gives, at each of its points,
finitely many original charts inside the subspace whose union contains the
trace of an ambient neighborhood. -/
theorem exists_chart_finset_of_isQuasinet {Y : Set X}
    (hq : AtlasTopology.IsQuasinet
      (AtlasTopology.restrictedFamily (range fun i => range (a.chart i)) Y))
    (y : Y) :
    ∃ s : Finset a.Index, (∀ i ∈ s, range (a.chart i) ⊆ Y) ∧
      ∃ O ∈ 𝓝 (y : X), O ∩ Y ⊆ ⋃ i ∈ s, range (a.chart i) := by
  classical
  obtain ⟨σ, hσ, hστ, -, hN⟩ := hq y
  have hmem : ∀ S : σ, ∃ i, range (a.chart i) ⊆ Y ∧
      S.1 = Subtype.val ⁻¹' range (a.chart i) := by
    rintro ⟨S, hS⟩
    obtain ⟨_, ⟨i, rfl⟩, hVY, rfl⟩ := hστ hS
    exact ⟨i, hVY, rfl⟩
  choose f hfY hfS using hmem
  have : Fintype σ := hσ.fintype
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · intro i hi
    obtain ⟨S, -, rfl⟩ := Finset.mem_image.mp hi
    exact hfY S
  · obtain ⟨O, hO, hOsub⟩ := (mem_nhds_subtype Y y _).mp hN
    refine ⟨O, hO, ?_⟩
    rintro z ⟨hzO, hzY⟩
    obtain ⟨S, hS, hzS⟩ := mem_sUnion.mp (hOsub (show (⟨z, hzY⟩ : Y) ∈ Subtype.val ⁻¹' O from hzO))
    have hz : (⟨z, hzY⟩ : Y) ∈ Subtype.val ⁻¹' range (a.chart (f ⟨S, hS⟩)) :=
      hfS ⟨S, hS⟩ ▸ hzS
    exact mem_iUnion₂.mpr ⟨f ⟨S, hS⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), hz⟩

namespace RecognizedSubset

variable {a}

theorem isCompact_locus (W : a.RecognizedSubset) : IsCompact W.locus := by
  rw [← W.range_chart]
  exact isCompact_range W.chart.continuous

/-- At one point of a recognized subset, a finite family of recognized
neighbors whose union is a neighborhood is refined by finitely many original
charts, each inside the subset and one family member. -/
theorem exists_goodChart_finset_at (W : a.RecognizedSubset)
    (𝓕 : a.RecognizedSubset → Prop) {x : X} (hxW : x ∈ W.locus)
    {I : Set a.RecognizedSubset} (hI : I.Finite)
    (hIx : ∀ T ∈ I, x ∈ T.locus ∧ 𝓕 T) (hN : (⋃ T ∈ I, T.locus) ∈ 𝓝 x) :
    ∃ s : Finset a.Index,
      (∀ i ∈ s, ∃ T, 𝓕 T ∧ range (a.chart i) ⊆ W.locus ∩ T.locus) ∧
        ∃ O ∈ 𝓝 x, O ∩ W.locus ⊆ ⋃ i ∈ s, range (a.chart i) := by
  classical
  have hloc : ∀ T : I, ∃ s : Finset a.Index,
      (∀ i ∈ s, range (a.chart i) ⊆ W.locus ∩ T.1.locus) ∧
        ∃ O ∈ 𝓝 x, O ∩ (W.locus ∩ T.1.locus) ⊆ ⋃ i ∈ s, range (a.chart i) := by
    intro T
    have hq := a.isNet_chartFamily.isQuasinet_restrictedFamily_inter
      W.val.isQuasinet_restrictedChartFamily T.1.val.isQuasinet_restrictedChartFamily
    exact a.exists_chart_finset_of_isQuasinet hq ⟨x, hxW, (hIx T.1 T.2).1⟩
  choose s hs O hO hOsub using hloc
  have : Fintype I := hI.fintype
  refine ⟨Finset.univ.biUnion s, ?_, ?_⟩
  · intro i hi
    obtain ⟨T, -, hiT⟩ := Finset.mem_biUnion.mp hi
    exact ⟨T.1, (hIx T.1 T.2).2, hs T i hiT⟩
  · refine ⟨(⋃ T ∈ I, T.locus) ∩ ⋂ T : I, O T,
      inter_mem hN (iInter_mem.mpr hO), ?_⟩
    rintro z ⟨⟨hzN, hzO⟩, hzW⟩
    obtain ⟨T, hT, hzT⟩ := mem_iUnion₂.mp hzN
    have hz := hOsub ⟨T, hT⟩ ⟨mem_iInter.mp hzO ⟨T, hT⟩, hzW, hzT⟩
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_biUnion.mpr ⟨⟨T, hT⟩, Finset.mem_univ _, hi⟩, hzi⟩

/-- Compactness of a recognized subset turns pointwise finite recognized
neighborhood families into one finite cover by original charts, each inside
the subset and one family member. -/
theorem exists_goodChart_finset (W : a.RecognizedSubset)
    (𝓕 : a.RecognizedSubset → Prop)
    (h : ∀ x ∈ W.locus, ∃ I : Set a.RecognizedSubset, I.Finite ∧
      (∀ T ∈ I, x ∈ T.locus ∧ 𝓕 T) ∧ (⋃ T ∈ I, T.locus) ∈ 𝓝 x) :
    ∃ s : Finset a.Index,
      (∀ i ∈ s, ∃ T, 𝓕 T ∧ range (a.chart i) ⊆ W.locus ∩ T.locus) ∧
        W.locus ⊆ ⋃ i ∈ s, range (a.chart i) := by
  classical
  have hpt : ∀ x ∈ W.locus, ∃ s : Finset a.Index,
      (∀ i ∈ s, ∃ T, 𝓕 T ∧ range (a.chart i) ⊆ W.locus ∩ T.locus) ∧
        ∃ O ∈ 𝓝 x, O ∩ W.locus ⊆ ⋃ i ∈ s, range (a.chart i) := by
    intro x hx
    obtain ⟨I, hI, hIx, hN⟩ := h x hx
    exact W.exists_goodChart_finset_at 𝓕 hx hI hIx hN
  choose s hs O hO hOsub using hpt
  obtain ⟨t, ht⟩ := W.isCompact_locus.elim_nhds_subcover' O hO
  refine ⟨t.biUnion (fun x => s x.1 x.2), ?_, ?_⟩
  · intro i hi
    obtain ⟨x, -, hix⟩ := Finset.mem_biUnion.mp hi
    exact hs x.1 x.2 i hix
  · intro z hz
    obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.mp (ht hz)
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hOsub x.1 x.2 ⟨hzx, hz⟩)
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_biUnion.mpr ⟨x, hxt, hi⟩, hzi⟩

end RecognizedSubset

end Langlands.Analytic.IndexedAffinoidAtlas

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open Set IndexedAffinoidAtlas PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
  (V : Set A.space) (U : Set B.space)

/-- A recognized target affinoid inside `U` with a supplied recognized full
preimage in `V` whose actual full-recognition pair pullback is finite. -/
def FiniteTargetMember (T : B.atlas.saturatedAtlas.RecognizedSubset) : Prop :=
  T.locus ⊆ U ∧ ∃ (P : A.atlas.saturatedAtlas.RecognizedSubset)
    (h : g.baseMap '' Set.range P.chart ⊆ Set.range T.chart),
    P.locus = V ∩ g.baseMap ⁻¹' T.locus ∧
      (g.fullRecognitionPairs.pullback P T h).IsFiniteBanach

/-- The literal hypothesis of `FiniteOverTargetLocalityStatement`: finite
families of such members at every target point of `U`, whose union is a
neighborhood of the point. -/
def HasFiniteTargetFamilies : Prop :=
  ∀ x ∈ U, ∃ I : Set B.atlas.saturatedAtlas.RecognizedSubset,
    I.Finite ∧
    (∀ W ∈ I, x ∈ W.locus ∧ W.locus ⊆ U ∧
      ∃ (P : A.atlas.saturatedAtlas.RecognizedSubset)
        (h : g.baseMap '' Set.range P.chart ⊆ Set.range W.chart),
        P.locus = V ∩ g.baseMap ⁻¹' W.locus ∧
          (g.fullRecognitionPairs.pullback P W h).IsFiniteBanach) ∧
    (⋃ W ∈ I, W.locus) ∈ 𝓝 x

/-- A finite cover of a recognized target affinoid by original saturated
charts, each contained in the affinoid and in one supplied family member,
together with that member's supplied finite recognized full preimage. -/
structure FamilyRefinement (W : B.atlas.saturatedAtlas.RecognizedSubset) where
  size : ℕ
  index : Fin size → B.atlas.saturatedAtlas.Index
  target : Fin size → B.atlas.saturatedAtlas.RecognizedSubset
  index_subset : ∀ k,
    range (B.atlas.saturatedAtlas.chart (index k)) ⊆ W.locus ∩ (target k).locus
  covers : W.locus ⊆ ⋃ k, range (B.atlas.saturatedAtlas.chart (index k))
  target_subset : ∀ k, (target k).locus ⊆ U
  left : Fin size → A.atlas.saturatedAtlas.RecognizedSubset
  left_admissible : ∀ k, g.baseMap '' range (left k).chart ⊆ range (target k).chart
  left_locus : ∀ k, (left k).locus = V ∩ g.baseMap ⁻¹' (target k).locus
  left_finite : ∀ k,
    (g.fullRecognitionPairs.pullback (left k) (target k) (left_admissible k)).IsFiniteBanach

variable {g V U}

theorem HasFiniteTargetFamilies.exists_goodChart (hfam : g.HasFiniteTargetFamilies V U)
    (W : B.atlas.saturatedAtlas.RecognizedSubset) (hWU : W.locus ⊆ U) :
    ∃ s : Finset B.atlas.saturatedAtlas.Index,
      (∀ i ∈ s, ∃ T, g.FiniteTargetMember V U T ∧
        range (B.atlas.saturatedAtlas.chart i) ⊆ W.locus ∩ T.locus) ∧
        W.locus ⊆ ⋃ i ∈ s, range (B.atlas.saturatedAtlas.chart i) :=
  W.exists_goodChart_finset (g.FiniteTargetMember V U) fun x hx => by
    obtain ⟨I, hI, hIx, hN⟩ := hfam x (hWU hx)
    exact ⟨I, hI, fun T hT => ⟨(hIx T hT).1, (hIx T hT).2⟩, hN⟩

/-- The constructed finite chart refinement of a target affinoid in `U`. -/
def HasFiniteTargetFamilies.refinement (hfam : g.HasFiniteTargetFamilies V U)
    (W : B.atlas.saturatedAtlas.RecognizedSubset) (hWU : W.locus ⊆ U) :
    g.FamilyRefinement V U W := by
  classical
  choose s hgood hcov using hfam.exists_goodChart W hWU
  let e : Fin s.card ≃ s := s.equivFin.symm
  choose T hT hET using fun k : Fin s.card => hgood (e k).1 (e k).2
  choose P hP hPloc hPfin using fun k => (hT k).2
  refine ⟨s.card, fun k => (e k).1, T, hET, ?_, fun k => (hT k).1, P, hP, hPloc, hPfin⟩
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcov hx)
  refine mem_iUnion.mpr ⟨e.symm ⟨i, hi⟩, ?_⟩
  rw [Equiv.apply_symm_apply]
  exact hxi

namespace FamilyRefinement

variable {W : B.atlas.saturatedAtlas.RecognizedSubset} (F : g.FamilyRefinement V U W)

theorem index_subset_locus (k : Fin F.size) :
    range (B.atlas.saturatedAtlas.chart (F.index k)) ⊆ W.locus :=
  (F.index_subset k).trans inter_subset_left

theorem index_subset_target (k : Fin F.size) :
    range (B.atlas.saturatedAtlas.chart (F.index k)) ⊆ (F.target k).locus :=
  (F.index_subset k).trans inter_subset_right

/-- The refinement charts as actual full domains of the target affinoid. -/
def domain (k : Fin F.size) : Domain K W.algebra :=
  W.originalDomain (F.index k) (F.index_subset_locus k)

/-- The finite full-domain cover of the whole target affinoid spectrum. -/
def cover : Domain.FiniteCover (Domain.whole K W.algebra) where
  size := F.size
  obj := F.domain
  map k := ⟨(F.domain k).baseMap, rfl⟩
  covers x _ := by
    have hx : W.chart x ∈ W.locus := W.range_chart ▸ mem_range_self x
    obtain ⟨k, hk⟩ := mem_iUnion.mp (F.covers hx)
    exact ⟨k, hk⟩

/-- The identity map of the target with the chart cover and the actual
restrictions of the family members to the refinement charts. -/
def rightCover : (StrongHom.id B.saturatedPresentation).RecognizedOpenImageCover W U where
  cover := F.cover
  target := F.target
  target_subset := F.target_subset
  pullback k := (F.target k).originalRestriction (F.index k) (F.index_subset_target k)
  chart_comm k x :=
    ((F.target k).chart_originalRestriction (F.index k) (F.index_subset_target k) x).trans
      (W.originalDomain_over_ambient (F.index k) (F.index_subset_locus k) x).symm

/-- The finite local base-change models over the refinement. -/
def models : FiniteOpenBaseChangeModels g (StrongHom.id B.saturatedPresentation) V U W where
  rightCover := F.rightCover
  left := F.left
  left_admissible := F.left_admissible
  left_locus := F.left_locus
  left_finite := F.left_finite

end FamilyRefinement

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
