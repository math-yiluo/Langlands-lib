import Langlands.Geometry.Analytic.FiniteChartFieldPointPullbacks
import Langlands.Geometry.Analytic.LocalizedChartCoverLifts
import Langlands.Geometry.Analytic.LocalizedPullbackDescent
import Langlands.Geometry.Analytic.QuasiEtaleRigidity.RefinementGluing
import Langlands.Geometry.Analytic.SpaceAnalytificationAffinoidChartNeighborhoods

/-! # Gluing localized maps on chart covers and refining maps into chart covers -/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits Set

namespace Langlands.Analytic.SaturatedAtlasPresentation

open IndexedAffinoidAtlas.OriginalChartDomain
open SourceCategory
open scoped Topology

section Gluing

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : SaturatedAtlasPresentation.{u, v, v} K}

private theorem comparison_map_domainInclusion' (A : SaturatedAtlasPresentation.{u, v, v} K)
    (D : A.presentation.atlas.OriginalChartDomain) :
    comparisonFunctor.map (SourceCategory.domainInclusion A D) =
      localizationFunctor.map (A.originalDomainInclusion D) :=
  sourceHomEquiv.apply_symm_apply _

/-- Localized maps on the small spectra of a quasinet of charts glue to a localized map
on the whole object, provided any two of them agree after precomposition with every pair
of maps into their charts having the same composite with the chart inclusions. -/
theorem exists_hom_of_chartCover {ι : Type w}
    (i : ι → A.presentation.atlas.Index)
    (hi : AtlasTopology.LocallyRefines
      (range (fun k => range (A.presentation.atlas.chart (i k)))) {univ})
    {Y : LocalizedCategory.{u, v, v} (K := K)}
    (l : ∀ k, localizationFunctor.obj (A.smallChartSpectrum (i k)) ⟶ Y)
    (hl : ∀ (k j : ι) (T : LocalizedCategory.{u, v, v} (K := K))
      (a : T ⟶ localizationFunctor.obj (A.smallChartSpectrum (i k)))
      (b : T ⟶ localizationFunctor.obj (A.smallChartSpectrum (i j))),
      a ≫ localizationFunctor.map (A.smallChartSpectrumInclusion (i k)) =
        b ≫ localizationFunctor.map (A.smallChartSpectrumInclusion (i j)) →
      a ≫ l k = b ≫ l j) :
    ∃ L : localizationFunctor.obj A ⟶ Y,
      ∀ k, localizationFunctor.map (A.smallChartSpectrumInclusion (i k)) ≫ L = l k := by
  classical
  obtain ⟨V₀, hV⟩ := localizedObjectEquiv.surjective Y
  change localizationFunctor.obj V₀ = Y at hV
  subst Y
  let D := fun k => ofChart (i k)
  let e := fun k => localizationFunctor.mapIso (A.smallChartDomainIso (i k))
  let δ := fun k => (e k).inv ≫ l k
  have hincl (k : ι) : localizationFunctor.map (A.smallChartSpectrumInclusion (i k)) =
      (e k).hom ≫ localizationFunctor.map (A.originalDomainInclusion (D k)) := by
    rw [← smallChartDomainIso_hom_comp_inclusion, Functor.map_comp]
    rfl
  have hd (k : ι) :
      (e k).inv ≫ localizationFunctor.map (A.smallChartSpectrumInclusion (i k)) =
        localizationFunctor.map (A.originalDomainInclusion (D k)) := by
    rw [hincl, Iso.inv_hom_id_assoc]
  let nested {S T : A.presentation.atlas.OriginalChartDomain} (hST : S ≤ T) :
      localizationFunctor.obj (A.originalDomain S) ⟶ localizationFunctor.obj (A.originalDomain T) :=
    comparisonFunctor.map (SourceCategory.domainMap hST)
  have hnested {S T : A.presentation.atlas.OriginalChartDomain} (hST : S ≤ T) :
      nested hST ≫ localizationFunctor.map (A.originalDomainInclusion T) =
        localizationFunctor.map (A.originalDomainInclusion S) := by
    have h := (Functor.map_comp comparisonFunctor (SourceCategory.domainMap hST)
      (SourceCategory.domainInclusion A T)).symm.trans
        (congrArg comparisonFunctor.map (domainMap_inclusion hST))
    exact (congrArg (nested hST ≫ ·) (comparison_map_domainInclusion' A T).symm).trans
      (h.trans (comparison_map_domainInclusion' A S))
  let localMap (k : ι) : ofPresentation (A.originalDomain (D k)) ⟶ ofPresentation V₀ :=
    sourceHomEquiv.symm (δ k)
  have hlocalMap (k : ι) : comparisonFunctor.map (localMap k) = δ k :=
    sourceHomEquiv.apply_symm_apply _
  let family : QuotientDomainMatchingFamily A V₀ D :=
    { localMap := localMap
      overlap := fun k j => by
        apply comparisonFunctor.map_injective
        rw [Functor.map_comp, Functor.map_comp, hlocalMap, hlocalMap]
        change nested (inf_le_left : D k ⊓ D j ≤ D k) ≫ (e k).inv ≫ l k =
          nested (inf_le_right : D k ⊓ D j ≤ D j) ≫ (e j).inv ≫ l j
        rw [← Category.assoc, ← Category.assoc]
        apply hl
        rw [Category.assoc, Category.assoc, hd, hd, hnested, hnested] }
  let L : localizationFunctor.obj A ⟶ localizationFunctor.obj V₀ :=
    comparisonFunctor.map (family.glue hi)
  have hL (k : ι) : localizationFunctor.map (A.originalDomainInclusion (D k)) ≫ L = δ k := by
    have h := congrArg comparisonFunctor.map (family.glue_restrict hi k)
    rw [Functor.map_comp, comparison_map_domainInclusion'] at h
    exact h.trans (hlocalMap k)
  refine ⟨L, fun k => ?_⟩
  rw [hincl, Category.assoc, hL]
  exact Iso.hom_inv_id_assoc _ _

end Gluing

section Refinement

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, u, u} K}

private theorem smallChartSpectrumInclusion_comp'
    {S T : SaturatedAtlasPresentation.{u, u, u} K} (F : S ⟶ T)
    (m : S.presentation.atlas.Index) (j : T.presentation.atlas.Index)
    (h : F.baseMap '' range (S.presentation.atlas.chart m) ⊆
      range (T.presentation.atlas.chart j)) :
    S.smallChartSpectrumInclusion m ≫ F =
      SmallAffinoidSpectrum.map.{u, u} (F.pullback m j h) ≫ T.smallChartSpectrumInclusion j := by
  let R := S.presentation.atlas.algebra m
  let Q := T.presentation.atlas.algebra j
  let g := F.pullback m j h
  have h₁ := SmallAffinoidSpectrum.chartMap_comp R m (BoundedAlgHom.id K R) F j h
  have h₂ := SmallAffinoidSpectrum.map_comp_chartMap.{u, u} g j (BoundedAlgHom.id K Q)
  rw [BoundedAlgHom.id_comp] at h₁
  rw [BoundedAlgHom.comp_id] at h₂
  exact h₁.trans h₂.symm

/-- Let a family of charts of `A` form a quasinet. Every localized map into `A` becomes,
after precomposition with a quasi-isomorphism, a map whose source has a quasinet of
charts each of whose small spectra maps into the small spectrum of a chart of the
family, compatibly with the chart inclusions. -/
theorem exists_chartCover_refinement {ι : Type w}
    (i : ι → A.presentation.atlas.Index)
    (hi : AtlasTopology.LocallyRefines
      (range (fun k => range (A.presentation.atlas.chart (i k)))) {univ})
    (f : localizationFunctor.obj B ⟶ localizationFunctor.obj A) :
    ∃ (S : SaturatedAtlasPresentation.{u, u, u} K) (s : S ⟶ B), s.IsQuasiIso ∧
      ∃ J : Set S.presentation.atlas.Index,
      AtlasTopology.LocallyRefines
        (range (fun m : J => range (S.presentation.atlas.chart m.val))) {univ} ∧
      ∀ m : J, ∃ (k : ι) (g : localizationFunctor.obj (S.smallChartSpectrum m.val) ⟶
          localizationFunctor.obj (A.smallChartSpectrum (i k))),
        g ≫ localizationFunctor.map (A.smallChartSpectrumInclusion (i k)) =
          localizationFunctor.map (S.smallChartSpectrumInclusion m.val) ≫
            localizationFunctor.map s ≫ f := by
  classical
  obtain ⟨S, s, hs, F, -, hF, -⟩ := exists_commonStrongNumerators f f
  let J : Set S.presentation.atlas.Index :=
    {m | ∃ k, F.baseMap '' range (S.presentation.atlas.chart m) ⊆
      range (A.presentation.atlas.chart (i k))}
  refine ⟨S, s, hs, J, ?_, ?_⟩
  · rintro U hU y -
    obtain rfl := mem_singleton_iff.mp hU
    obtain ⟨τ, hτfin, hτsub, hyτ, hτn⟩ := hi univ (mem_singleton _) (F.baseMap y) (mem_univ _)
    rw [nhdsWithin_univ] at hτn
    have key : ∀ V ∈ τ, ∃ k : ι, range (A.presentation.atlas.chart (i k)) = V :=
      fun V hV => hτsub hV
    choose k hk using key
    have hcov (V : τ) := isLocallyChartCovered_preimage F (i (k V.1 V.2))
      (y := y) ((hk V.1 V.2).symm ▸ (hyτ V.1 V.2).2)
    choose σ hσfin hσ N hN hNcov using hcov
    have : Finite τ := hτfin.to_subtype
    let ρ : Set (Set S.presentation.space) :=
      ⋃ V : τ, (fun m => range (S.presentation.atlas.chart m)) '' σ V
    refine ⟨ρ, finite_iUnion fun V => (hσfin V).image _, ?_, ?_, ?_⟩
    · rintro _ hW
      obtain ⟨V, m, hm, rfl⟩ := by simpa only [ρ, mem_iUnion, mem_image] using hW
      refine ⟨⟨m, k V.1 V.2, ?_⟩, rfl⟩
      rintro _ ⟨t, ht, rfl⟩
      exact (hσ V m hm).2.1 ht
    · rintro _ hW
      obtain ⟨V, m, hm, rfl⟩ := by simpa only [ρ, mem_iUnion, mem_image] using hW
      exact ⟨subset_univ _, (hσ V m hm).1⟩
    · rw [nhdsWithin_univ]
      have hpre : F.baseMap ⁻¹' ⋃₀ τ ∈ 𝓝 y :=
        F.baseMap.continuous.continuousAt.preimage_mem_nhds hτn
      apply Filter.mem_of_superset (Filter.inter_mem hpre (Filter.iInter_mem.mpr hN))
      rintro z ⟨⟨V, hV, hzV⟩, hzN⟩
      have hzk : F.baseMap z ∈ range (A.presentation.atlas.chart (i (k V hV))) :=
        (hk V hV).symm ▸ hzV
      obtain ⟨m, hm, hzm⟩ := mem_iUnion₂.mp
        (hNcov ⟨V, hV⟩ ⟨hzk, mem_iInter.mp hzN ⟨V, hV⟩⟩)
      exact ⟨_, mem_iUnion.mpr ⟨⟨V, hV⟩, mem_image_of_mem _ hm⟩, hzm⟩
  · rintro ⟨m, k, hm⟩
    refine ⟨k, localizationFunctor.map (SmallAffinoidSpectrum.map.{u, u} (F.pullback m (i k) hm)),
      ?_⟩
    have h := congrArg localizationFunctor.map (smallChartSpectrumInclusion_comp' F m (i k) hm)
    rw [Functor.map_comp, ← hF] at h
    exact (localizationFunctor.map_comp _ _).symm.trans h.symm

end Refinement

end Langlands.Analytic.SaturatedAtlasPresentation
