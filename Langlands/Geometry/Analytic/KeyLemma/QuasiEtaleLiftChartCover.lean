import Langlands.Geometry.Analytic.KeyLemma.LiftChartCover
import Langlands.Geometry.Analytic.RefinedDomainEtaleFactorization
import Langlands.Geometry.Analytic.QuasiEtaleDomainChartCover
import Langlands.Geometry.Analytic.QuasiEtaleRigidity.StrongNearPostcomposition
import Langlands.Geometry.Analytic.StrongNearDomainTransport

/-! # Lift charts through a quasi-étale factorization -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open BanachSpectrum CategoryTheory PresentedAffinoidAlgebra Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, v} K}

private theorem spectralLiftsOver_comp_of_represents
    {R S T : PresentedAffinoidAlgebra K} (f : BoundedAlgHom K R S)
    (i : BoundedAlgHom K S T) {L : Set (BanachSpectrum S)} (hi : Represents K i L)
    (hf : f.HasSpectralLiftsOver Set.univ) :
    (i.comp f).HasSpectralLiftsOver Set.univ := by
  have hTransfer : i.HasSpectralTestTransfer :=
    (⟨T, i, L, hi⟩ : Domain K S).hasSpectralTestTransfer
  intro F ε hε
  obtain ⟨E, η, hη, he⟩ := hTransfer F ε hε
  obtain ⟨D, δ, hδ, hd⟩ := hf E η hη
  refine ⟨D, δ, hδ, fun P a b _ hb => ?_⟩
  obtain ⟨a₀, h₀, h₀close⟩ := hd P (a.comp i) b (fun _ => Set.mem_univ _) hb
  obtain ⟨a', ha', hclose⟩ := he P a a₀ h₀close
  refine ⟨a', ?_, hclose⟩
  change (a'.comp i).comp f = b
  rwa [ha']

private theorem spectralLiftsOver_of_comp_represents_univ
    {R S T : PresentedAffinoidAlgebra K} (f : BoundedAlgHom K R S)
    (i : BoundedAlgHom K S T) (hi : Represents K i Set.univ)
    (hf : (i.comp f).HasSpectralLiftsOver Set.univ) :
    f.HasSpectralLiftsOver Set.univ := by
  classical
  intro E ε hε
  obtain ⟨D, δ, hδ, hd⟩ := hf (E.image i) ε hε
  refine ⟨D, δ, hδ, fun P a b _ hb => ?_⟩
  obtain ⟨a₀, ha₀, _⟩ := hi.2.2 P a (fun _ => Set.mem_univ _)
  have ha (s : S) : a₀ (i s) = a s := congrArg (fun m : BoundedAlgHom K S P => m s) ha₀
  have hb₀ (r : R) (hr : r ∈ D) :
      SpectralBound (b r - a₀ (i.comp f r)) δ := by
    change SpectralBound (b r - a₀ (i (f r))) δ
    rw [ha]
    exact hb r hr
  obtain ⟨a', ha', hclose⟩ := hd P a₀ b (fun _ => Set.mem_univ _) hb₀
  refine ⟨a'.comp i, ha', fun s hs => ?_⟩
  change SpectralBound (a' (i s) - a s) ε
  rw [← ha]
  exact hclose (i s) (Finset.mem_image_of_mem i hs)

private theorem spectralLiftChart_of_square
    {T : SaturatedAtlasPresentation.{u, v, v} K}
    (g : ofSaturation A ⟶ ofSaturation B) (h : ofSaturation C ⟶ ofSaturation B)
    (a : T ⟶ ofSaturation A) (b : T ⟶ ofSaturation C) (hSquare : a ≫ g = b ≫ h)
    (m : T.presentation.atlas.Index) (c : (ofSaturation A).presentation.atlas.Index)
    (k : (ofSaturation C).presentation.atlas.Index)
    (ha : Set.range ((ofSaturation A).presentation.atlas.chart c) =
      a.baseMap '' Set.range (T.presentation.atlas.chart m))
    (hb : b.baseMap '' Set.range (T.presentation.atlas.chart m) ⊆
      Set.range ((ofSaturation C).presentation.atlas.chart k))
    (haRep : Represents K (a.pullback m c ha.symm.subset) Set.univ)
    {L : Set (BanachSpectrum ((ofSaturation C).presentation.atlas.algebra k))}
    (hbRep : Represents K (b.pullback m k hb) L) (hk : IsSpectralLiftChart h k) :
    IsSpectralLiftChart g c := by
  obtain ⟨w, hkw, hLift⟩ := hk
  have hbg : (b ≫ h).baseMap '' Set.range (T.presentation.atlas.chart m) ⊆
      Set.range ((ofSaturation B).presentation.atlas.chart w) := by
    rintro _ ⟨t, ht, rfl⟩
    exact hkw ⟨b.baseMap t, hb ⟨t, ht, rfl⟩, rfl⟩
  have hcw : g.baseMap '' Set.range ((ofSaturation A).presentation.atlas.chart c) ⊆
      Set.range ((ofSaturation B).presentation.atlas.chart w) := by
    rw [ha, ← Set.image_comp]
    change (a ≫ g).baseMap '' Set.range (T.presentation.atlas.chart m) ⊆ _
    rwa [hSquare]
  have hag : (a ≫ g).baseMap '' Set.range (T.presentation.atlas.chart m) ⊆
      Set.range ((ofSaturation B).presentation.atlas.chart w) := hSquare.symm ▸ hbg
  have hEq : (a.pullback m c ha.symm.subset).comp (g.pullback c w hcw) =
      (b.pullback m k hb).comp (h.pullback k w hkw) :=
    (comp_pullback_eq a g m c w ha.symm.subset hcw hag).symm.trans
      ((pullback_congr hSquare m w hag hbg).trans (comp_pullback_eq b h m k w hb hkw hbg))
  refine ⟨w, hcw, spectralLiftsOver_of_comp_represents_univ _ _ haRep ?_⟩
  rw [hEq]
  exact spectralLiftsOver_comp_of_represents _ _ hbRep hLift

private theorem domainInclusion_image_chart
    (T : SaturatedAtlasPresentation.{u, v, v} K) (D : T.AnalyticDomain)
    (j : (T.domain D).presentation.atlas.Index) :
    (T.domainInclusion D).baseMap '' Set.range ((T.domain D).presentation.atlas.chart j) =
      Set.range (T.presentation.atlas.chart j.val) := by
  ext t
  constructor
  · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨_, Set.mem_range_self p, rfl⟩

private theorem exists_spectralLiftChart_image
    (g : ofSaturation A ⟶ ofSaturation B)
    (i : (ofSaturation A).presentation.atlas.Index)
    (d : RefinedDomainEtaleFactorization
      ((ofSaturation A).domainInclusion ((ofSaturation A).chartDomain i) ≫ g))
    (m : d.source.presentation.atlas.Index)
    (k : (ofSaturation d.envelope.presentation).presentation.atlas.Index)
    (hk : IsSpectralLiftChart (d.envelope.saturationIso.hom ≫ d.map) k)
    (hb : (d.toDomain ≫ d.envelope.domainInclusion d.domain ≫ d.envelope.saturationIso.inv).baseMap ''
      Set.range (d.source.presentation.atlas.chart m) ⊆
      Set.range ((ofSaturation d.envelope.presentation).presentation.atlas.chart k)) :
    ∃ c : (ofSaturation A).presentation.atlas.Index,
      Set.range ((ofSaturation A).presentation.atlas.chart c) =
        (d.toSource ≫ (ofSaturation A).domainInclusion ((ofSaturation A).chartDomain i)).baseMap ''
          Set.range (d.source.presentation.atlas.chart m) ∧ IsSpectralLiftChart g c := by
  let a := d.toSource ≫ (ofSaturation A).domainInclusion ((ofSaturation A).chartDomain i)
  let e := d.envelope.saturationIso
  let b := d.toDomain ≫ d.envelope.domainInclusion d.domain ≫ e.inv
  let h := e.hom ≫ d.map
  have hSquare : a ≫ g = b ≫ h := by
    simpa only [a, b, h, Category.assoc, Iso.inv_hom_id_assoc] using d.comm
  obtain ⟨c, hc, hcEq, hcRep⟩ := exists_chart_image_of_isQuasiIso d.toSource_isQuasiIso m
  have ha : Set.range ((ofSaturation A).presentation.atlas.chart c.val) =
      a.baseMap '' Set.range (d.source.presentation.atlas.chart m) := by
    change _ = (((ofSaturation A).domainInclusion ((ofSaturation A).chartDomain i)).baseMap ∘
      d.toSource.baseMap) '' Set.range (d.source.presentation.atlas.chart m)
    rw [Set.image_comp, ← hcEq, domainInclusion_image_chart]
  have haRep : Represents K (a.pullback m c.val ha.symm.subset) Set.univ := by
    exact (originalDomainInclusion_comp_pullback ((ofSaturation A).chartDomain i)
      d.toSource m c hc ha.symm.subset).symm ▸ hcRep
  obtain ⟨j, hj, hjEq, hjRep⟩ := exists_chart_image_of_isQuasiIso d.toDomain_isQuasiIso m
  have hImage : b.baseMap '' Set.range (d.source.presentation.atlas.chart m) =
      e.inv.baseMap '' Set.range (d.envelope.presentation.atlas.chart j.val) := by
    change (e.inv.baseMap ∘ (d.envelope.domainInclusion d.domain).baseMap ∘ d.toDomain.baseMap) ''
      Set.range (d.source.presentation.atlas.chart m) = _
    rw [Set.image_comp, Set.image_comp, ← hjEq, domainInclusion_image_chart]
  have hjk : e.inv.baseMap '' Set.range (d.envelope.presentation.atlas.chart j.val) ⊆
      Set.range ((ofSaturation d.envelope.presentation).presentation.atlas.chart k) :=
    hImage ▸ hb
  have hInc : (d.envelope.domainInclusion d.domain ≫ e.inv).baseMap ''
      Set.range ((d.envelope.domain d.domain).presentation.atlas.chart j) ⊆
      Set.range ((ofSaturation d.envelope.presentation).presentation.atlas.chart k) := by
    change (e.inv.baseMap ∘ (d.envelope.domainInclusion d.domain).baseMap) '' Set.range _ ⊆ _
    rw [Set.image_comp, domainInclusion_image_chart]
    exact hjk
  have hPull : b.pullback m k hb = (d.toDomain.pullback m j hj).comp (e.inv.pullback j.val k hjk) :=
    (comp_pullback_eq d.toDomain (d.envelope.domainInclusion d.domain ≫ e.inv) m j k hj hInc hb).trans
      (congrArg (fun q => (d.toDomain.pullback m j hj).comp q)
        (domainInclusion_comp_pullback e.inv d.domain j k hjk hInc))
  have hRep := (isQuasiIso_of_isIso e.inv).2 j.val k hjk
  have hbRep := hRep.comp hjRep
  exact ⟨c.val, ha, spectralLiftChart_of_square g h a b hSquare m c.val k ha hb haRep
    (hPull.symm ▸ hbRep) hk⟩

private theorem exists_finite_spectralLiftChart_cover_of_factorization
    (g : ofSaturation A ⟶ ofSaturation B) (i : (ofSaturation A).presentation.atlas.Index)
    (hfac : HasDomainEtaleFactorization ((ofSaturation A).localizedDomainInclusion
      ((ofSaturation A).chartDomain i) ≫ localizationFunctor.map g)) :
    ∃ s : Finset (ofSaturation A).presentation.atlas.Index,
      (∀ c ∈ s, IsSpectralLiftChart g c) ∧
      ∀ y ∈ Set.range ((ofSaturation A).presentation.atlas.chart i),
        ∃ c ∈ s, y ∈ Set.range ((ofSaturation A).presentation.atlas.chart c) := by
  classical
  let Y := ofSaturation A
  let D := Y.chartDomain i
  have hfac' : HasDomainEtaleFactorization
      (localizationFunctor.map (Y.domainInclusion D ≫ g)) := by
    rw [Functor.map_comp]
    exact hfac
  let d := refinedDomainEtaleFactorization (Y.domainInclusion D ≫ g) hfac'
  let a := d.toSource ≫ Y.domainInclusion D
  let Z := ofSaturation d.envelope.presentation
  let e := d.envelope.saturationIso
  let b := d.toDomain ≫ d.envelope.domainInclusion d.domain ≫ e.inv
  let h := e.hom ≫ d.map
  have hEtale : AffinoidAtlasPresentation.StrongHom.IsEtaleAllPieces
      (A := d.envelope.presentation) (B := B) h :=
    (strongEtale_ofSaturation_iff h).mp
      (strongEtale_comp (strongEtale_of_isQuasiIso _ (isQuasiIso_of_isIso e.hom)) d.isEtale)
  let Q (m : d.source.presentation.atlas.Index) :=
    ∃ c : Y.presentation.atlas.Index,
      Set.range (Y.presentation.atlas.chart c) =
        a.baseMap '' Set.range (d.source.presentation.atlas.chart m) ∧ IsSpectralLiftChart g c
  have hLocal (x : d.source.presentation.space) :
      d.source.IsLocallyChartCovered Q Set.univ x := by
    obtain ⟨J, hJ, hJm, N, hN, hcov⟩ :=
      isLocallyChartCovered_isSpectralLiftChart_and_isRigidChart h hEtale
        (⊤ : Z.AnalyticDomain) (y := b.baseMap x) (Set.mem_univ _)
    let : Finite J := hJ.to_subtype
    let Zs (j : J) := b.baseMap ⁻¹' Set.range (Z.presentation.atlas.chart j.val)
    refine isLocallyChartCovered_of_cover (Zs := Zs) (fun _ => Set.subset_univ _)
      (N₀ := b.baseMap ⁻¹' N) (b.baseMap.continuous.continuousAt.preimage_mem_nhds hN) ?_ ?_
    · intro x' hx'
      obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp
        (hcov ⟨Set.mem_univ _, hx'.2⟩)
      exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hxj⟩
    · intro j
      have hj := hJm j.val j.property
      refine (isLocallyChartCovered_preimage b j.val hj.1).of_subset_pred fun m hm => ?_
      apply exists_spectralLiftChart_image g i d m j.val hj.2.2.1
      rintro _ ⟨p, hp, rfl⟩
      exact hm hp
  let : CompactSpace (Y.domain D).presentation.space :=
    isCompact_iff_compactSpace.mp (Y.isCompactDomain_chartDomain i).1
  let : CompactSpace d.source.presentation.space :=
    d.toSource_isQuasiIso.1.homeomorph.symm.compactSpace
  choose σ hσ hσData N hN hcover using hLocal
  obtain ⟨points, _, hpoints⟩ :=
    isCompact_univ.elim_nhds_subcover N (fun x _ => hN x)
  let selected : Set d.source.presentation.atlas.Index :=
    ⋃ t ∈ (points : Set d.source.presentation.space), σ t
  have hselected : selected.Finite := points.finite_toSet.biUnion (fun t _ => hσ t)
  have hQ (m : selected) : Q m.val := by
    obtain ⟨t, _, hm⟩ := Set.mem_iUnion₂.mp m.property
    exact (hσData t m.val hm).2.2
  choose c hcEq hcLift using hQ
  let : Fintype selected := hselected.fintype
  refine ⟨Finset.univ.image c, fun k hk => ?_, fun y hy => ?_⟩
  · obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hk
    exact hcLift m
  · obtain ⟨x, hx⟩ := d.toSource_isQuasiIso.1.homeomorph.surjective
      (⟨y, hy⟩ : (Y.domain D).presentation.space)
    have hax : a.baseMap x = y :=
      congrArg (fun p => (Y.domainInclusion D).baseMap p) hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp (hpoints (Set.mem_univ x))
    obtain ⟨m, hm, hxm⟩ := Set.mem_iUnion₂.mp (hcover t ⟨Set.mem_univ _, hxt⟩)
    let m₀ : selected := ⟨m, Set.mem_iUnion₂.mpr ⟨t, ht, hm⟩⟩
    refine ⟨c m₀, Finset.mem_image_of_mem c (Finset.mem_univ _), ?_⟩
    rw [hcEq m₀]
    exact ⟨x, hxm, hax⟩

private theorem locallyRefines_univ_of_finite_closed_cover
    {X I : Type*} [TopologicalSpace X] (s : Finset I) (V : I → Set X)
    (hClosed : ∀ i ∈ s, IsClosed (V i)) (hCover : ∀ x : X, ∃ i ∈ s, x ∈ V i) :
    AtlasTopology.LocallyRefines (Set.range (fun i : (s : Set I) => V i.val)) {Set.univ} := by
  classical
  intro U hU x _
  rcases Set.mem_singleton_iff.mp hU with rfl
  let inside := s.filter (fun i => x ∈ V i)
  let outside := s.filter (fun i => x ∉ V i)
  let σ := V '' (inside : Set I)
  refine ⟨σ, inside.finite_toSet.image V, ?_, ?_, ?_⟩
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨⟨i, (Finset.mem_filter.mp hi).1⟩, rfl⟩
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨Set.subset_univ _, (Finset.mem_filter.mp hi).2⟩
  have hOutside : IsClosed (⋃ i ∈ outside, V i) :=
    isClosed_biUnion_finset fun i hi => hClosed i (Finset.mem_filter.mp hi).1
  have hx : x ∈ (⋃ i ∈ outside, V i)ᶜ := by
    intro hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact (Finset.mem_filter.mp hi).2 hxi
  rw [nhdsWithin_univ]
  refine Filter.mem_of_superset (hOutside.isOpen_compl.mem_nhds hx) fun y hy => ?_
  obtain ⟨i, hi, hyi⟩ := hCover y
  have hxi : x ∈ V i := by
    by_contra hnot
    exact hy (Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hnot⟩, hyi⟩)
  exact ⟨V i, ⟨i, Finset.mem_filter.mpr ⟨hi, hxi⟩, rfl⟩, hyi⟩

/-- Finitely many lift charts have ranges that locally refine the whole
source. The finite range family can be used for strong-map gluing. -/
def HasFiniteLiftChartCover (g : ofSaturation A ⟶ ofSaturation B) : Prop :=
  ∃ s : Finset (ofSaturation A).presentation.atlas.Index,
    (∀ c ∈ s, IsLiftChart g c) ∧
    AtlasTopology.LocallyRefines
      (Set.range (fun c : (s : Set (ofSaturation A).presentation.atlas.Index) =>
        Set.range ((ofSaturation A).presentation.atlas.chart c.val))) {Set.univ}

/-- A compact Hausdorff source of a quasi-étale strong map has a finite
locally refining cover by lift charts. -/
theorem IsQuasiEtale.hasFiniteLiftChartCover
    {g : ofSaturation A ⟶ ofSaturation B} (hg : IsQuasiEtale g)
    [CompactSpace A.space] [T2Space A.space] :
    HasFiniteLiftChartCover g := by
  classical
  let : T2Space (ofSaturation A).presentation.space := ‹T2Space A.space›
  obtain ⟨s₀, hfac, hcov₀⟩ := hg.exists_finite_domainEtale_chart_cover
  choose pieces hLift hCov using fun i : (s₀ : Set (ofSaturation A).presentation.atlas.Index) =>
    exists_finite_spectralLiftChart_cover_of_factorization g i.val (hfac i.val i.property)
  let s := Finset.univ.biUnion pieces
  refine ⟨s, fun c hc => ?_, locallyRefines_univ_of_finite_closed_cover s
    (fun c => Set.range ((ofSaturation A).presentation.atlas.chart c)) ?_ ?_⟩
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hc
    exact (hLift i c hi).isLiftChart
  · intro c _
    exact (isCompact_range ((ofSaturation A).presentation.atlas.isEmbedding_chart c).continuous).isClosed
  · intro x
    obtain ⟨i, hi, hxi⟩ := hcov₀ x
    obtain ⟨c, hc, hxc⟩ := hCov ⟨i, hi⟩ x hxi
    exact ⟨c, Finset.mem_biUnion.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, hc⟩, hxc⟩

end Langlands.Analytic.SaturatedAtlasPresentation
