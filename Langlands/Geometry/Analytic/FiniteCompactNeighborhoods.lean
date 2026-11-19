import Langlands.Geometry.Analytic.RecognizedFinitePullback
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteBanachPushout.Proof

/-! # Local finiteness from finite compact neighborhoods -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

/-- A point in the interior of a compact Hausdorff source piece with finite
fibre has an ambient open neighborhood which is relatively clopen over a
smaller target neighborhood. -/
theorem exists_isClopenOver_compact
    {Y : Type v} {X : Type w} [TopologicalSpace Y] [TopologicalSpace X]
    {f : Y → X} (hf : Continuous f) {C : Set Y} (hC : IsCompact C) [T2Space C]
    {D : Set X} (hD : IsCompact D) [T2Space D] (hCD : f '' C ⊆ D)
    {y : Y} (hy : y ∈ interior C) (hx : f y ∈ interior D)
    (hF : (C ∩ f ⁻¹' {f y}).Finite) :
    ∃ O U, IsClopenOver f C (f y) O U ∧ y ∈ O ∧ U ⊆ D := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let fC : C → X := fun z => f z.val
  let yC : C := ⟨y, interior_subset hy⟩
  have hpre : (Set.univ ∩ fC ⁻¹' D : Set C) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    exact ⟨Set.mem_univ _, hCD ⟨z.val, z.property, rfl⟩⟩
  have hFC : (Set.univ ∩ fC ⁻¹' {f y} : Set C).Finite :=
    (hF.preimage Subtype.val_injective.injOn).subset fun z hz => ⟨z.property, hz.2⟩
  have hN : (⋃ _ : Unit, D) ∈ 𝓝 (f y) := by
    rw [Set.iUnion_const]
    exact mem_interior_iff_mem_nhds.mp hx
  have hV : (Subtype.val ⁻¹' interior C : Set C) ∈ 𝓝 yC :=
    (isOpen_interior.preimage continuous_subtype_val).mem_nhds hy
  obtain ⟨Orel, U, ⟨hOrel, -, hU, hxU, hcl⟩, hyOrel, hOint, hUD⟩ :=
    @exists_isClopenOver_of_finite_fibre C X _ _ fC
      (hf.comp continuous_subtype_val) Set.univ isOpen_univ (f y) D
      inferInstance Unit inferInstance (fun _ => D) (fun _ => hD)
      (fun _ => Set.Subset.refl _) (fun _ => interior_subset hx) hN
      (fun _ => hpre.symm ▸ isCompact_univ)
      (fun _ => hpre.symm ▸ inferInstance) hFC yC (Set.mem_univ _) rfl
      (Subtype.val ⁻¹' interior C) hV
  obtain ⟨G, hG, hGeq⟩ := isOpen_induced_iff.mp hOrel
  let O : Set Y := G ∩ interior C
  have hOeq : O = Subtype.val '' Orel := by
    ext z
    constructor
    · rintro ⟨hzG, hzC⟩
      exact ⟨⟨z, interior_subset hzC⟩, hGeq ▸ hzG, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(hGeq.symm ▸ hz : z ∈ Subtype.val ⁻¹' G), hOint hz⟩
  refine ⟨O, U, ⟨hG.inter isOpen_interior,
    fun z hz => interior_subset hz.2, hU, hxU, ?_⟩, ?_, ?_⟩
  · rintro z ⟨⟨hzC, hzU⟩, hzcl⟩
    have hzrel : (⟨z, hzC⟩ : C) ∈ closure Orel := by
      rw [closure_subtype]
      rw [← hOeq]
      exact hzcl
    rw [hOeq]
    exact ⟨⟨z, hzC⟩, hcl ⟨⟨Set.mem_univ _, hzU⟩, hzrel⟩, rfl⟩
  · rw [hOeq]
    exact ⟨yC, hyOrel, rfl⟩
  · exact hUD.trans (Set.iUnion_subset fun _ => Set.Subset.refl _)

namespace AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {g : StrongHom A.saturatedPresentation B.saturatedPresentation}

/-- A finite morphism between recognized compact pieces is finite at every
point lying in the interiors of the source and target pieces. -/
theorem IsFiniteOver.isFiniteAt_of_mem_interior
    (C : A.atlas.saturatedAtlas.RecognizedSubset)
    (D : B.atlas.saturatedAtlas.RecognizedSubset)
    (hg : g.IsFiniteOver C.locus D.locus) {y : A.space}
    (hy : y ∈ interior C.locus) (hx : g.baseMap y ∈ interior D.locus) :
    g.IsFiniteAt y := by
  have hF := hg.finite_fibre D (Set.Subset.refl _) (interior_subset hx)
  have hCc : IsCompact C.locus := isCompact_iff_compactSpace.mpr inferInstance
  have hDc : IsCompact D.locus := isCompact_iff_compactSpace.mpr inferInstance
  have hCt : T2Space C.locus := inferInstance
  have hDt : T2Space D.locus := inferInstance
  obtain ⟨O, U, ⟨hO, hOC, hU, hxU, hcl⟩, hyO, hUD⟩ :=
    @exists_isClopenOver_compact A.space B.space _ _ g.baseMap
      g.baseMap.continuous C.locus hCc hCt D.locus hDc hDt hg.1 y hy hx hF
  refine ⟨O ∩ g.baseMap ⁻¹' U, U,
    hO.inter (hU.preimage g.baseMap.continuous), hU, ⟨hyO, hxU⟩, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hz.2
  · intro W hW
    obtain ⟨P, hPmap, hPloc, hPfin⟩ := hg.2 W (hW.trans hUD)
    have hclP : P.locus ∩ closure O ⊆ O := by
      rintro z ⟨hzP, hzcl⟩
      rw [hPloc] at hzP
      exact hcl ⟨⟨hzP.1, hW hzP.2⟩, hzcl⟩
    have hQloc : (A.atlas.clopenPiece P hO hclP).locus =
        (O ∩ g.baseMap ⁻¹' U) ∩ g.baseMap ⁻¹' W.locus := by
      refine (A.atlas.clopenPiece_locus P hO hclP).trans ?_
      ext z
      constructor
      · rintro ⟨hzP, hzO⟩
        have hzP' : z ∈ C.locus ∩ g.baseMap ⁻¹' W.locus := hPloc ▸ hzP
        exact ⟨⟨hzO, hW hzP'.2⟩, hzP'.2⟩
      · rintro ⟨⟨hzO, -⟩, hzW⟩
        exact ⟨hPloc.symm ▸ ⟨hOC hzO, hzW⟩, hzO⟩
    have hQr : Set.range (A.atlas.clopenPiece P hO hclP).chart ⊆ Set.range P.chart := by
      rw [(A.atlas.clopenPiece P hO hclP).range_chart, P.range_chart]
      exact A.atlas.clopenPiece_subset P hO hclP
    have hQmap : g.baseMap '' Set.range (A.atlas.clopenPiece P hO hclP).chart ⊆
        Set.range W.chart := (Set.image_mono hQr).trans hPmap
    refine ⟨A.atlas.clopenPiece P hO hclP, hQmap, hQloc, ?_⟩
    have hcomm := g.fullRecognitionPairs.restriction_comm (A.atlas.clopenPiece P hO hclP)
      P W W hQr (Set.Subset.refl _) hQmap hPmap
    rw [B.fullRecognitionPresentation.atlas.restriction_id W (Set.Subset.refl _),
      BoundedAlgHom.comp_id] at hcomm
    rw [← hcomm]
    exact (A.atlas.isFiniteBanach_restriction_clopenPiece P hO hclP).comp hPfin

/-- A finite Banach chart map is finite over the two chart ranges in the
full-recognition sense. -/
theorem isFiniteOver_of_charts
    (i : A.atlas.saturatedAtlas.Index) (j : B.atlas.saturatedAtlas.Index)
    (hij : g.baseMap '' range (A.atlas.saturatedAtlas.chart i) ⊆
      range (B.atlas.saturatedAtlas.chart j))
    (hfin : (g.pullback i j hij).IsFiniteBanach) :
    g.IsFiniteOver (range (A.atlas.saturatedAtlas.chart i))
      (range (B.atlas.saturatedAtlas.chart j)) := by
  refine ⟨hij, fun W hW => ?_⟩
  let V := g.recognizedPullback W i j hW hij
  have hV := g.recognizedPullback_locus W i j hW hij
  have hadm := g.recognizedPullback_admissible W i j hW hij
  exact ⟨V, hadm, hV, g.fullRecognitionPairs_isFiniteBanach_of_pushout
    W i j hW hij AffinoidPushout.finiteBanachPushout hfin V
    (hV.subset.trans inter_subset_left) hadm hV⟩

/-- A finite Banach chart map gives finiteness at points in the interiors
of both chart ranges. -/
theorem isFiniteAt_of_finite_charts
    (i : A.atlas.saturatedAtlas.Index) (j : B.atlas.saturatedAtlas.Index)
    (hij : g.baseMap '' range (A.atlas.saturatedAtlas.chart i) ⊆
      range (B.atlas.saturatedAtlas.chart j))
    (hfin : (g.pullback i j hij).IsFiniteBanach) {y : A.space}
    (hy : y ∈ interior (range (A.atlas.saturatedAtlas.chart i)))
    (hx : g.baseMap y ∈ interior (range (B.atlas.saturatedAtlas.chart j))) :
    g.IsFiniteAt y := by
  exact (isFiniteOver_of_charts i j hij hfin).isFiniteAt_of_mem_interior
    (A.atlas.saturatedAtlas.originalRecognitionIndex i)
    (B.atlas.saturatedAtlas.originalRecognitionIndex j) hy hx

end AffinoidAtlasPresentation.StrongHom

end Langlands.Analytic
