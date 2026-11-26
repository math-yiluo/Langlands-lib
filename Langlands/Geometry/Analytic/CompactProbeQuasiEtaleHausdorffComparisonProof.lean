import Langlands.Geometry.Analytic.CompactProbeQuasiEtaleHausdorffComparisonStatement
import Langlands.Geometry.Analytic.CompactQuasiEtalePullbacksProof
import Langlands.Geometry.Analytic.LocalizedQuasiEtaleLocality
import Langlands.Geometry.Analytic.QuasiEtaleRelativePullbackPoints
import Langlands.Geometry.Analytic.RecognizedDomainSaturationSite

/-! # Quasi-étale covering comparison on Hausdorff objects -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits Filter Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : LocalizedCategory.{u, v, v} (K := K)}

/-- If every point of a compact set has a neighbourhood that is the union of finitely many
members of `T`, then finitely many members of `T` cover the compact set. -/
private theorem finite_subcover_of_chart_neighborhoods
    {Y : Type v} [TopologicalSpace Y] {C : Set Y} (hC : IsCompact C) (T : Set (Set Y))
    (hT : ∀ x ∈ C, ∃ σ : Set (Set Y), σ.Finite ∧ ⋃₀ σ ∈ 𝓝 x ∧ σ ⊆ T) :
    ∃ σ : Set (Set Y), σ.Finite ∧ C ⊆ ⋃₀ σ ∧ σ ⊆ T := by
  classical
  choose σ hfinite hnhds hsub using hT
  obtain ⟨s, hs⟩ := hC.elim_nhds_subcover' (fun x hx => ⋃₀ σ x hx) hnhds
  refine ⟨⋃ x : s, σ x.val.val x.val.property, Set.finite_iUnion fun x => hfinite _ _, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, V, hV, hyV⟩ := mem_iUnion₂.mp (hs hy)
    exact ⟨V, mem_iUnion.mpr ⟨⟨x, hx⟩, hV⟩, hyV⟩
  · intro V hV
    obtain ⟨x, hx⟩ := mem_iUnion.mp hV
    exact hsub x.val.val x.val.property hx

/-- In a Hausdorff object, a compact set lies in a compact analytic domain: the union of
finitely many atlas charts covering it. -/
private theorem exists_compact_domain_containing
    (A : LocalizedCategory.{u, v, v} (K := K)) [T2Space (localizedSpaceFunctor.obj A)]
    {C : Set (localizedSpaceFunctor.obj A)} (hC : IsCompact C) :
    ∃ D : (presentationOf A).AnalyticDomain, IsCompactSpace (domainObj A D) ∧ C ⊆ D.carrier := by
  classical
  let a := (presentationOf A).presentation.atlas
  obtain ⟨σ, hσ, hcharts, hcover⟩ := a.isNet_chartFamily.1.exists_finite_cover_of_isCompact hC
  choose i hi using fun V : σ => hcharts V.property
  let F : σ → Set (localizedSpaceFunctor.obj A) := fun V => range (a.chart (i V))
  let Dset := ⋃ V, F V
  let : Finite σ := hσ.to_subtype
  let : T2Space (presentationOf A).presentation.space :=
    inferInstanceAs (T2Space (localizedSpaceFunctor.obj A))
  let : T2Space Dset := inferInstanceAs (T2Space (Subtype (fun x => x ∈ Dset)))
  let D : (presentationOf A).AnalyticDomain :=
    ⟨Dset, a.isOriginalChartDomain_of_finite_chart_cover Dset i rfl⟩
  have hD : (presentationOf A).IsCompactDomain D :=
    (presentationOf A).isCompactDomain_of_eq_iUnion D i rfl
  refine ⟨D, ⟨isCompact_iff_compactSpace.mp hD.1, hD.2⟩, ?_⟩
  intro x hx
  obtain ⟨V, hV, hxV⟩ := mem_sUnion.mp (hcover hx)
  let W : σ := ⟨V, hV⟩
  have hW : F W = V := hi W
  exact mem_iUnion.mpr ⟨W, hW.symm ▸ hxV⟩

/-- An analytic domain of a Hausdorff site object, as a site object over the same base. -/
private def domainSiteObject (U : QuasiEtaleSite X)
    [T2Space (localizedSpaceFunctor.obj U.left)] (D : (presentationOf U.left).AnalyticDomain) :
    QuasiEtaleSite X :=
  MorphismProperty.Over.mk ⊤ (domainι U.left D ≫ U.hom)
    ((hasLocalDomainEtaleFactorizations_of_quasiEtale (U := U.left) U.prop).domainι_comp D).quasiEtale

/-- The inclusion of an analytic domain as an arrow of the site. -/
private def domainSiteInclusion (U : QuasiEtaleSite X)
    [T2Space (localizedSpaceFunctor.obj U.left)] (D : (presentationOf U.left).AnalyticDomain) :
    domainSiteObject U D ⟶ U :=
  MorphismProperty.Over.homMk (domainι U.left D) rfl trivial

/-- An arrow whose image lies in an analytic domain factors through that domain. -/
private def domainSiteLift {T U : QuasiEtaleSite X}
    [T2Space (localizedSpaceFunctor.obj U.left)] (D : (presentationOf U.left).AnalyticDomain)
    (f : T ⟶ U) (hf : ∀ y, localizedSpaceFunctor.map f.left y ∈ D.carrier) :
    T ⟶ domainSiteObject U D :=
  MorphismProperty.Over.homMk (domainLift D f.left hf) (by
    change domainLift D f.left hf ≫ domainι U.left D ≫ U.hom = T.hom
    rw [← Category.assoc, domainLift_comp, MorphismProperty.Over.w]) trivial

/-- The factorization through a domain recovers the original arrow. -/
private theorem domainSiteLift_comp {T U : QuasiEtaleSite X}
    [T2Space (localizedSpaceFunctor.obj U.left)] (D : (presentationOf U.left).AnalyticDomain)
    (f : T ⟶ U) (hf : ∀ y, localizedSpaceFunctor.map f.left y ∈ D.carrier) :
    domainSiteLift D f hf ≫ domainSiteInclusion U D = f :=
  MorphismProperty.Over.Hom.ext (domainLift_comp D f.left hf)

/-- A covering sieve on a Hausdorff object has chart-image neighbourhoods: probe it with a
compact domain containing a compact neighbourhood of the point. -/
private theorem has_chart_neighborhoods_of_compact_probes {U : QuasiEtaleSite X}
    [T2Space (localizedSpaceFunctor.obj U.left)] {S : Sieve U}
    (hS : S ∈ compactProbeQuasiEtaleTopology X U) : HasQuasiEtaleChartNeighborhoods S.arrows := by
  classical
  intro x
  let a := (presentationOf U.left).presentation.atlas
  let : WeaklyLocallyCompactSpace (localizedSpaceFunctor.obj U.left) :=
    a.isNet_chartFamily.1.weaklyLocallyCompactSpace
      (fun V hV => (a.isCompactFamily_chartFamily V hV).1)
  obtain ⟨C, hC, hCn⟩ := exists_compact_mem_nhds x
  obtain ⟨D, hD, hCD⟩ := exists_compact_domain_containing U.left hC
  let g := domainSiteInclusion U D
  obtain ⟨n, V, f, hV, hf, hsurj⟩ := hS g hD
  choose σ hσ hσchart hσcovers using fun i =>
    let : CompactSpace (localizedSpaceFunctor.obj (V i).left) := (hV i).1
    (presentationOf (V i).left).presentation.atlas.isNet_chartFamily.1
      |>.exists_finite_cover_of_isCompact (isCompact_univ (X := localizedSpaceFunctor.obj (V i).left))
  let H : Fin n → Set (Set (localizedSpaceFunctor.obj U.left)) :=
    fun i => (Set.image (localizedSpaceFunctor.map (f i ≫ g).left)) '' σ i
  refine ⟨⋃ i, H i, Set.finite_iUnion fun i => (hσ i).image _, ?_, ?_⟩
  · refine Filter.mem_of_superset hCn fun y hy => ?_
    let yd : (compactProbePointFunctor X).obj (domainSiteObject U D) := ⟨y, hCD hy⟩
    obtain ⟨i, z, hz⟩ := hsurj yd
    obtain ⟨W, hW, hzW⟩ := mem_sUnion.mp (hσcovers i (mem_univ z))
    refine ⟨localizedSpaceFunctor.map (f i ≫ g).left '' W,
      mem_iUnion.mpr ⟨i, ⟨W, hW, rfl⟩⟩, z, hzW, ?_⟩
    change (compactProbePointFunctor X).map (f i ≫ g) z = y
    rw [Functor.map_comp_apply, hz]
    exact domainι_apply D yd
  · intro T hT
    obtain ⟨i, hTi⟩ := mem_iUnion.mp hT
    obtain ⟨W, hW, rfl⟩ := hTi
    obtain ⟨j, rfl⟩ := hσchart i hW
    exact ⟨V i, f i ≫ g, j, hf i, rfl⟩

/-- Compact parts of a quasi-étale space are covered by finitely many charts
whose restrictions to the base are quasi-étale. -/
private theorem exists_compact_quasiEtale_charts (V : QuasiEtaleSite X)
    {C : Set (localizedSpaceFunctor.obj V.left)} (hC : IsCompact C) :
    ∃ (σ : Set (Set (localizedSpaceFunctor.obj V.left))), σ.Finite ∧ C ⊆ ⋃₀ σ ∧
      ∀ W ∈ σ, ∃ i : (presentationOf V.left).presentation.atlas.Index,
        W = ((presentationOf V.left).chartDomain i).carrier ∧
        quasiEtale (domainι V.left ((presentationOf V.left).chartDomain i) ≫ V.hom) := by
  let Good (W : Set (localizedSpaceFunctor.obj V.left)) : Prop :=
    ∃ i : (presentationOf V.left).presentation.atlas.Index,
      W = ((presentationOf V.left).chartDomain i).carrier ∧
      quasiEtale (domainι V.left ((presentationOf V.left).chartDomain i) ≫ V.hom)
  apply finite_subcover_of_chart_neighborhoods hC {W | Good W}
  intro y _
  obtain ⟨F, hF, hn, hs⟩ := isLocalizedQuasiEtaleAt_of_quasiEtale V.prop y
  refine ⟨F, hF, hn, fun W hW => ?_⟩
  obtain ⟨i, hi, T, t, j, ht, hj, heq⟩ := hs W hW
  exact ⟨i, hi.symm, heq ▸ quasiEtale_comp_of_isAffinoidDomainEmbedding_of_etale j hj t ht⟩

/-- Under the chart-neighbourhood condition, finitely many images of arrows of the sieve
with compact Hausdorff sources cover any compact subset of the target. -/
private theorem compact_images_cover_of_chart_neighborhoods {U : QuasiEtaleSite X}
    {S : Sieve U} (hS : HasQuasiEtaleChartNeighborhoods S.arrows)
    {C : Set (localizedSpaceFunctor.obj U.left)} (hC : IsCompact C) :
    ∃ σ : Set (Set (localizedSpaceFunctor.obj U.left)), σ.Finite ∧ C ⊆ ⋃₀ σ ∧
      ∀ R ∈ σ, ∃ (V : QuasiEtaleSite X) (f : V ⟶ U),
        IsCompactSpace V.left ∧ S f ∧ R = range (localizedSpaceFunctor.map f.left) := by
  classical
  let Good (R : Set (localizedSpaceFunctor.obj U.left)) : Prop :=
    ∃ (V : QuasiEtaleSite X) (f : V ⟶ U),
      IsCompactSpace V.left ∧ S f ∧ R = range (localizedSpaceFunctor.map f.left)
  apply finite_subcover_of_chart_neighborhoods hC {R | Good R}
  intro x _
  obtain ⟨σ, hf, hn, hs⟩ := hS x
  have hpiece (R : Set (localizedSpaceFunctor.obj U.left)) (hR : R ∈ σ) :
      ∃ δ : Set (Set (localizedSpaceFunctor.obj U.left)), δ.Finite ∧ R ⊆ ⋃₀ δ ∧
        ∀ W ∈ δ, Good W := by
    obtain ⟨V, f, i, hfS, rfl⟩ := hs R hR
    obtain ⟨δ, hδ, hcov, hgood⟩ := exists_compact_quasiEtale_charts V
      ((presentationOf V.left).isCompactDomain_chartDomain i).1
    refine ⟨(Set.image (localizedSpaceFunctor.map f.left)) '' δ, hδ.image _, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨W, hW, hyW⟩ := mem_sUnion.mp (hcov hy)
      exact ⟨_, ⟨W, hW, rfl⟩, y, hyW, rfl⟩
    · rintro _ ⟨W, hW, rfl⟩
      obtain ⟨j, rfl, hj⟩ := hgood W hW
      let E := (presentationOf V.left).chartDomain j
      let W : QuasiEtaleSite X := MorphismProperty.Over.mk ⊤ (domainι V.left E ≫ V.hom) hj
      let p : W ⟶ V := MorphismProperty.Over.homMk (domainι V.left E) rfl trivial
      refine ⟨W, p ≫ f, isCompactSpace_chartDomainObj _ j, S.downward_closed hfS p, ?_⟩
      have hp (t : localizedSpaceFunctor.obj W.left) :
          localizedSpaceFunctor.map (p ≫ f).left t = localizedSpaceFunctor.map f.left t.val := by
        rw [MorphismProperty.Comma.comp_left, Functor.map_comp, TopCat.comp_app]
        exact congrArg (localizedSpaceFunctor.map f.left) (domainι_apply E t)
      ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t, ht⟩, hp ⟨t, ht⟩⟩
      · rintro ⟨t, rfl⟩
        exact ⟨t.val, t.property, (hp t).symm⟩
  choose! δ hδ hsub hgood using hpiece
  refine ⟨⋃ R ∈ σ, δ R, hf.biUnion hδ, Filter.mem_of_superset hn ?_, ?_⟩
  · rintro y ⟨R, hR, hyR⟩
    obtain ⟨W, hW, hyW⟩ := mem_sUnion.mp (hsub R hR hyR)
    exact ⟨W, mem_iUnion₂.mpr ⟨R, hR, hW⟩, hyW⟩
  · intro W hW
    obtain ⟨R, hR, hWR⟩ := mem_iUnion₂.mp hW
    exact hgood R hR W hWR

/-- The chart-neighbourhood condition on a Hausdorff object implies the compact-probe test:
pull back finitely many compact members of the sieve along the probe over a compact domain. -/
private theorem compact_probes_of_has_chart_neighborhoods {U : QuasiEtaleSite X}
    [T2Space (localizedSpaceFunctor.obj U.left)] {S : Sieve U}
    (hS : HasQuasiEtaleChartNeighborhoods S.arrows) : S ∈ compactProbeQuasiEtaleTopology X U := by
  classical
  intro C g hC
  let : CompactSpace (localizedSpaceFunctor.obj C.left) := hC.1
  have hc : IsCompact (range (localizedSpaceFunctor.map g.left)) :=
    isCompact_range (localizedSpaceFunctor.map g.left).hom.continuous
  obtain ⟨σ, hf, hcov, hs⟩ := compact_images_cover_of_chart_neighborhoods hS hc
  let : Fintype σ := hf.fintype
  let e := Fintype.equivFin σ
  choose V f hV hfS hR using fun R : σ => hs R.val R.property
  let B : Set (localizedSpaceFunctor.obj U.left) :=
    range (localizedSpaceFunctor.map g.left) ∪ ⋃ R : σ, range (localizedSpaceFunctor.map (f R).left)
  have hB : IsCompact B := hc.union (isCompact_iUnion fun R => by
    let : CompactSpace (localizedSpaceFunctor.obj (V R).left) := (hV R).1
    exact isCompact_range (localizedSpaceFunctor.map (f R).left).hom.continuous)
  obtain ⟨D, hD, hBD⟩ := exists_compact_domain_containing U.left hB
  have hgD (y : localizedSpaceFunctor.obj C.left) :
      localizedSpaceFunctor.map g.left y ∈ D.carrier :=
    hBD (Or.inl (mem_range_self y))
  have hfD (R : σ) (y : localizedSpaceFunctor.obj (V R).left) :
      localizedSpaceFunctor.map (f R).left y ∈ D.carrier :=
    hBD (Or.inr (mem_iUnion.mpr ⟨R, mem_range_self y⟩))
  let g' := domainSiteLift D g hgD
  let f' (R : σ) := domainSiteLift D (f R) (hfD R)
  have hg' : g' ≫ domainSiteInclusion U D = g := domainSiteLift_comp _ _ _
  have hf' (R : σ) : f' R ≫ domainSiteInclusion U D = f R := domainSiteLift_comp _ _ _
  choose T hT hpb using fun R : σ =>
    compactQuasiEtalePullbacks (K := K) X (domainSiteObject U D) C (V R) g' (f' R) hD hC (hV R)
  refine ⟨_, fun k => (T (e.symm k)).pt, fun k => (T (e.symm k)).fst,
    fun k => hT (e.symm k), ?_, ?_⟩
  · intro k
    let R := e.symm k
    change S ((T R).fst ≫ g)
    rw [← hg', ← Category.assoc, (T R).condition, Category.assoc, hf']
    exact S.downward_closed (hfS R) (T R).snd
  · intro x
    obtain ⟨W, hW, hxW⟩ := mem_sUnion.mp (hcov (mem_range_self (f := localizedSpaceFunctor.map g.left) x))
    let R : σ := ⟨W, hW⟩
    obtain ⟨y, hy⟩ : localizedSpaceFunctor.map g.left x ∈ range (localizedSpaceFunctor.map (f R).left) :=
      hR R ▸ hxW
    have hcomm : localizedSpaceFunctor.map g'.left x = localizedSpaceFunctor.map (f' R).left y := by
      apply Subtype.ext
      have hgval : (localizedSpaceFunctor.map g'.left x).val = localizedSpaceFunctor.map g.left x :=
        val_domainLift_apply D g.left hgD x
      have hfval : (localizedSpaceFunctor.map (f' R).left y).val =
          localizedSpaceFunctor.map (f R).left y :=
        val_domainLift_apply D (f R).left (hfD R) y
      rw [hgval, hfval, hy]
    have hq : quasiEtale (g'.left ≫ (domainSiteObject U D).hom) := by
      rw [MorphismProperty.Over.w]
      exact C.prop
    obtain ⟨z, hz, -⟩ := exists_point_of_isPullback_over_compactQuasiEtale
      (domainSiteObject U D).hom (hpb R) hq (domainSiteObject U D).prop hD x y hcomm
    refine ⟨e R, ?_⟩
    change x ∈ range ((compactProbePointFunctor X).map (T (e.symm (e R))).fst)
    rw [e.symm_apply_apply]
    exact ⟨z, hz⟩

/-- On a Hausdorff site object the compact-probe topology has Berkovich's
chart-neighbourhood coverings. -/
theorem compactProbeQuasiEtaleHausdorffComparison (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] :
    CompactProbeQuasiEtaleHausdorffComparisonStatement.{u, v} K := by
  intro X U S hU
  let : T2Space (localizedSpaceFunctor.obj U.left) := hU
  exact ⟨has_chart_neighborhoods_of_compact_probes, compact_probes_of_has_chart_neighborhoods⟩

end Langlands.Analytic.SaturatedAtlasPresentation
