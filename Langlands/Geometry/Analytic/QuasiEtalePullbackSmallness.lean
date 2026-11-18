import Langlands.Geometry.Analytic.AffinoidDomainPushout
import Langlands.Geometry.Analytic.FibreProductLocalizedLimit
import Langlands.Geometry.Analytic.RecognitionFibreProductSmallness
import Langlands.Geometry.Analytic.RefinedDomainEtaleFactorization
import Langlands.Geometry.Analytic.StrongEtaleSourceOpenLocality

/-! # Smallness from domain–étale charts -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set PresentedAffinoidAlgebra AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : SaturatedAtlasPresentation.{u, v, v} K}

private theorem comp_image_subset (f : A ⟶ B) (g : B ⟶ C)
    {S : Set A.presentation.space} {T : Set B.presentation.space}
    {U : Set C.presentation.space}
    (hf : f.baseMap '' S ⊆ T) (hg : g.baseMap '' T ⊆ U) :
    (f ≫ g).baseMap '' S ⊆ U := by
  rw [baseMap_comp, ContinuousMap.coe_comp, Set.image_comp]
  exact (Set.image_mono hf).trans hg

private theorem represents_comp_pullback (f : A ⟶ B) (g : B ⟶ C)
    {i : A.presentation.atlas.Index} {j : B.presentation.atlas.Index}
    {k : C.presentation.atlas.Index}
    {hf : f.baseMap '' range (A.presentation.atlas.chart i) ⊆ range (B.presentation.atlas.chart j)}
    {hg : g.baseMap '' range (B.presentation.atlas.chart j) ⊆ range (C.presentation.atlas.chart k)}
    (h₁ : Represents K (f.pullback i j hf) (f.chartImageLocus i j))
    (h₂ : Represents K (g.pullback j k hg) (g.chartImageLocus j k)) :
    Represents K ((f ≫ g).pullback i k (comp_image_subset f g hf hg))
      ((f ≫ g).chartImageLocus i k) := by
  have hcomp : (f ≫ g).pullback i k (comp_image_subset f g hf hg) =
      (f.pullback i j hf).comp (g.pullback j k hg) :=
    f.saturatedComp_pullback g A.hasAllLocalDomains B.hasAllLocalDomains
      i j k hf hg (comp_image_subset f g hf hg)
  have hlocus : (f ≫ g).chartImageLocus i k =
      BanachSpectrum.comap (g.pullback j k hg).toBoundedRingHom '' f.chartImageLocus i j := by
    rw [← (f ≫ g).range_pullback i k (comp_image_subset f g hf hg),
      ← f.range_pullback i j hf, ← Set.range_comp, hcomp]
    rfl
  rw [hcomp, hlocus]
  exact h₂.comp h₁

private theorem exists_chart_of_represented_image (f : A ⟶ B)
    (i : A.presentation.atlas.Index) (j : B.presentation.atlas.Index)
    (h : f.baseMap '' range (A.presentation.atlas.chart i) ⊆ range (B.presentation.atlas.chart j))
    (hrep : Represents K (f.pullback i j h) (f.chartImageLocus i j)) :
    ∃ (k : B.presentation.atlas.Index)
      (e : BoundedAlgEquiv K (B.presentation.atlas.algebra k) (A.presentation.atlas.algebra i))
      (hk : f.baseMap '' range (A.presentation.atlas.chart i) = range (B.presentation.atlas.chart k)),
      f.pullback i k hk.subset = e.toBoundedAlgHom := by
  let D : Domain K (B.presentation.atlas.algebra j) :=
    ⟨A.presentation.atlas.algebra i, f.pullback i j h, f.chartImageLocus i j, hrep⟩
  let k := B.hasAllLocalDomains.domainChartIndex j D
  let e := (Domain.boundedEquivOfIso (B.hasAllLocalDomains.chartDomainIso j D)).symm
  have hk : f.baseMap '' range (A.presentation.atlas.chart i) = range (B.presentation.atlas.chart k) := by
    rw [B.hasAllLocalDomains.range_domainChartIndex j D]
    exact (Set.image_preimage_eq_of_subset h).symm
  refine ⟨k, e, hk, ?_⟩
  have hkj := B.hasAllLocalDomains.domainChartIndex_subset j D
  apply (B.presentation.atlas.restriction_represents k j hkj).hom_ext
  exact (f.pullback_comp_restriction i k j hkj hk.subset h).symm.trans
    (Domain.boundedEquivOfIso_symm_comp_baseMap (B.hasAllLocalDomains.chartDomainIso j D)).symm

private theorem exists_recognition_pair_small
    (f : A ⟶ C) (g : B ⟶ C) (i₀ : A.presentation.atlas.Index)
    (hF : HasDomainEtaleFactorization
      (localizationFunctor.map (A.domainInclusion (A.chartDomain i₀) ≫ f)))
    (y : A.presentation.space) (z : B.presentation.space)
    (hy : y ∈ range (A.presentation.atlas.chart i₀)) (hyz : f.baseMap y = g.baseMap z) :
    let F := CompatibleStrongHom.ofSaturated (recognitionMap f) (recognitionSource f).hasAllLocalDomains
    let G := CompatibleStrongHom.ofSaturated (recognitionMap g) (recognitionSource g).hasAllLocalDomains
    ∃ p : FibreProduct.PairIndex F G,
      y ∈ range ((recognitionSource f).presentation.atlas.chart p.val.1) ∧
      z ∈ range ((recognitionSource g).presentation.atlas.chart p.val.2) ∧
      Small.{v} (BanachSpectrum (FibreProduct.algebra F G p)) := by
  let D := A.chartDomain i₀
  let d := refinedDomainEtaleFactorization (A.domainInclusion D ≫ f) hF
  let a₀ := d.toSource ≫ A.domainInclusion D
  let b₀ := d.toDomain ≫ d.envelope.domainInclusion d.domain
  let a := a₀ ≫ recognitionSourceComparison f
  let b := b₀ ≫ recognitionSourceComparison d.map
  have hsquare : a ≫ recognitionMap f = b ≫ recognitionMap d.map := by
    have h := congrArg (fun m => m ≫ recognitionBaseComparison C) d.comm
    simpa only [a, b, a₀, b₀, Category.assoc, recognitionMap_square] using h
  obtain ⟨t, ht⟩ := d.toSource_isQuasiIso.1.homeomorph.surjective
    (⟨y, hy⟩ : (A.domain D).presentation.space)
  have hta : a.baseMap t = y := by
    change d.toSource.baseMap t = ⟨y, hy⟩ at ht
    exact congrArg (fun p => (A.domainInclusion D).baseMap p) ht
  have htb : d.map.baseMap (b.baseMap t) = g.baseMap z := by
    change (b ≫ recognitionMap d.map).baseMap t = _
    rw [← hsquare]
    change f.baseMap (a.baseMap t) = _
    rw [hta, hyz]
  obtain ⟨w, j, k, hw, hj, xw, xj, hxw, hxj, hfinite, -, -⟩ :=
    recognitionMaps_hasPointedFiniteEtalePairs d.map g d.isEtale (b.baseMap t) z htb
  obtain ⟨i, hi⟩ := (recognitionSource f).presentation.atlas.exists_mem_range_chart y
  obtain ⟨iA, hiA, hiAi⟩ := (recognitionSourceComparison f).exists_admissible_mem
    A.hasAllLocalDomains (a₀.baseMap t) i (hta ▸ hi)
  obtain ⟨iD, hiD, hiDA⟩ := (A.domainInclusion D).exists_admissible_mem
    (A.domain D).hasAllLocalDomains (d.toSource.baseMap t) iA hiA
  obtain ⟨mA, hmA, hmAD⟩ := d.toSource.exists_admissible_mem
    d.source.hasAllLocalDomains t iD hiD
  obtain ⟨iW, hiW, hiWw⟩ := (recognitionSourceComparison d.map).exists_admissible_mem
    d.envelope.hasAllLocalDomains (b₀.baseMap t) w ⟨xw, hxw⟩
  obtain ⟨iE, hiE, hiEW⟩ := (d.envelope.domainInclusion d.domain).exists_admissible_mem
    (d.envelope.domain d.domain).hasAllLocalDomains (d.toDomain.baseMap t) iW hiW
  obtain ⟨mW, hmW, hmWE⟩ := d.toDomain.exists_admissible_mem
    d.source.hasAllLocalDomains t iE hiE
  obtain ⟨m, hm, htm⟩ := IndexedAffinoidAtlas.exists_chart_inter hmA hmW
  have hmD := (Set.image_mono (hm.trans inter_subset_left)).trans hmAD
  have hmE := (Set.image_mono (hm.trans inter_subset_right)).trans hmWE
  have hma : a.baseMap '' range (d.source.presentation.atlas.chart m) ⊆
      range ((recognitionSource f).presentation.atlas.chart i) :=
    comp_image_subset a₀ _ (comp_image_subset _ _ hmD hiDA) hiAi
  have hmb : b.baseMap '' range (d.source.presentation.atlas.chart m) ⊆
      range ((recognitionSource d.map).presentation.atlas.chart w) :=
    comp_image_subset b₀ _ (comp_image_subset _ _ hmE hiEW) hiWw
  have hArep := represents_comp_pullback a₀ (recognitionSourceComparison f)
    (represents_comp_pullback d.toSource (A.domainInclusion D)
      (d.toSource_isQuasiIso.2 m iD hmD) ((domainInclusion_isDomainEmbedding A D).2 iD iA hiDA))
    ((recognitionSourceComparison_isQuasiIso f).2 iA i hiAi)
  have hWrep := represents_comp_pullback b₀ (recognitionSourceComparison d.map)
    (represents_comp_pullback d.toDomain (d.envelope.domainInclusion d.domain)
      (d.toDomain_isQuasiIso.2 m iE hmE)
      ((domainInclusion_isDomainEmbedding d.envelope d.domain).2 iE iW hiEW))
    ((recognitionSourceComparison_isQuasiIso d.map).2 iW w hiWw)
  obtain ⟨l, e, hl, hcoeff⟩ := exists_chart_of_represented_image a m i hma hArep
  have hlk : (recognitionMap f).baseMap '' range ((recognitionSource f).presentation.atlas.chart l) ⊆
      range ((recognitionBase C).presentation.atlas.chart k) := by
    rw [← hl, ← Set.image_comp]
    change (a ≫ recognitionMap f).baseMap '' _ ⊆ _
    rw [hsquare]
    exact comp_image_subset b _ hmb hw
  have hkv : (a ≫ recognitionMap f).baseMap '' range (d.source.presentation.atlas.chart m) ⊆
      range ((recognitionBase C).presentation.atlas.chart k) :=
    comp_image_subset a _ hl.subset hlk
  have hkw : (b ≫ recognitionMap d.map).baseMap '' range (d.source.presentation.atlas.chart m) ⊆
      range ((recognitionBase C).presentation.atlas.chart k) :=
    comp_image_subset b _ hmb hw
  have hal : (a ≫ recognitionMap f).pullback m k hkv =
      (a.pullback m l hl.subset).comp ((recognitionMap f).pullback l k hlk) :=
    a.saturatedComp_pullback (recognitionMap f)
      d.source.hasAllLocalDomains (recognitionSource f).hasAllLocalDomains m l k hl.subset hlk hkv
  have har : (b ≫ recognitionMap d.map).pullback m k hkw =
      (b.pullback m w hmb).comp ((recognitionMap d.map).pullback w k hw) :=
    b.saturatedComp_pullback (recognitionMap d.map)
      d.source.hasAllLocalDomains (recognitionSource d.map).hasAllLocalDomains m w k hmb hw hkw
  have halg : e.toBoundedAlgHom.comp ((recognitionMap f).pullback l k hlk) =
      (b.pullback m w hmb).comp ((recognitionMap d.map).pullback w k hw) := by
    rw [← hcoeff, ← hal, ← har]
    congr
  let E : Domain K ((recognitionSource d.map).presentation.atlas.algebra w) :=
    ⟨(recognitionSource f).presentation.atlas.algebra l,
      e.symm.toBoundedAlgHom.comp (b.pullback m w hmb), b.chartImageLocus m w,
      hWrep.postcomp_equiv e.symm⟩
  have hcomp : (recognitionMap f).pullback l k hlk =
      E.baseMap.comp ((recognitionMap d.map).pullback w k hw) := by
    apply BoundedAlgHom.ext
    intro x
    have h := congrArg (fun (a : BoundedAlgHom K _ _) => e.symm (a x)) halg
    simpa only [E, BoundedAlgHom.comp_apply, BoundedAlgEquiv.toBoundedAlgHom_apply,
      BoundedAlgEquiv.symm_apply_apply] using h
  let F := CompatibleStrongHom.ofSaturated (recognitionMap f) (recognitionSource f).hasAllLocalDomains
  let G := CompatibleStrongHom.ofSaturated (recognitionMap g) (recognitionSource g).hasAllLocalDomains
  let p : FibreProduct.PairIndex F G := ⟨(l, j), k, hlk, hj⟩
  refine ⟨p, ?_, ⟨xj, hxj⟩, ?_⟩
  · change y ∈ range ((recognitionSource f).presentation.atlas.chart l)
    exact hl ▸ ⟨t, htm, hta⟩
  · let : Small.{v} (BanachSpectrum ((recognitionSource g).presentation.atlas.algebra j)) :=
      small_of_injective ((recognitionSource g).presentation.atlas.isEmbedding_chart j).injective
    let hs : Small.{v} (BanachSpectrum
        (AffinoidPushout.algebra ((recognitionMap f).pullback l k hlk)
          ((recognitionMap g).pullback j k hj))) := by
      rw [hcomp]
      exact AffinoidPushout.small_spectrum_of_domain_finiteBanach
        ((recognitionMap d.map).pullback w k hw) ((recognitionMap g).pullback j k hj) E hfinite
    let : Small.{v} (BanachSpectrum (AffinoidPushout.algebra
        (F.pullback p.val.1 k hlk) (G.pullback p.val.2 k hj))) := hs
    exact small_of_injective
      (FibreProduct.commonBaseAlgebraEquiv F G p k ⟨hlk, hj⟩).spectrumHomeomorph.symm.injective

/-- The recognized product is small when each point of the first source
lies in a chart admitting a domain–étale factorization over the base. -/
theorem small_recognition_fibreProductSpace_of_domainEtaleCharts
    (f : A ⟶ C) (g : B ⟶ C)
    (hf : ∀ y : A.presentation.space, ∃ i : A.presentation.atlas.Index,
      y ∈ range (A.presentation.atlas.chart i) ∧ HasDomainEtaleFactorization
        (localizationFunctor.map (A.domainInclusion (A.chartDomain i) ≫ f))) :
    Small.{v} (FibreProduct.chartSystem (geometricCompatibleMap (recognitionMap f))
      (geometricCompatibleMap (recognitionMap g))).Space := by
  let F := geometricCompatibleMap (recognitionMap f)
  let G := geometricCompatibleMap (recognitionMap g)
  let C₀ := FibreProduct.chartSystem F G
  let S := {p : FibreProduct.PairIndex F G // Small.{v} (BanachSpectrum (FibreProduct.algebra F G p))}
  let : ∀ p : S, Small.{v} (BanachSpectrum (FibreProduct.algebra F G p.val)) := fun p => p.property
  apply small_of_surjective (f := fun t : Σ p : S, BanachSpectrum (FibreProduct.algebra F G p.val) =>
    C₀.chart t.1.val t.2)
  intro x
  let y := FibreProduct.fst F G x
  let z := FibreProduct.snd F G x
  obtain ⟨i, hy, hfactor⟩ := hf y
  obtain ⟨p, hyp, hzp, hsmall⟩ := exists_recognition_pair_small f g i hfactor y z hy
    (FibreProduct.baseMap_fst F G x)
  have hx : x ∈ range (C₀.chart p) := (FibreProduct.mem_range_chart_iff F G p x).2 ⟨hyp, hzp⟩
  obtain ⟨s, hs⟩ := hx
  exact ⟨⟨⟨p, hsmall⟩, s⟩, hs⟩

end Langlands.Analytic.SaturatedAtlasPresentation
