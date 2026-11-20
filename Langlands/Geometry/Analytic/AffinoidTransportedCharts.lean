import Langlands.Geometry.Analytic.AtlasTopology.CompactSubcover
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainTopology
import Langlands.Geometry.Analytic.InvariantAnalyticDomains
import Langlands.Geometry.Analytic.LocalizedChartCoverLifts
import Langlands.Geometry.Analytic.SmallAffinoidLocalizedMaps

/-! # Charts transported into an affinoid spectrum -/

noncomputable section

universe u

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K} {A : SaturatedAtlasPresentation.{u, u, u} K}

private abbrev smallSpectrum (R : PresentedAffinoidAlgebra K) :
    LocalizedCategory.{u, u, u} (K := K) :=
  localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, u} R)

set_option backward.isDefEq.respectTransparency false in
/-- A chart transported by a localized isomorphism to a small affinoid
spectrum is a full domain of the actual affinoid algebra. -/
def affinoidChartDomain (e : localizationFunctor.obj A ≅ smallSpectrum R)
    (i : A.presentation.atlas.Index) : Domain K R := by
  let T := A.presentation.atlas.algebra i
  let j : smallSpectrum T ⟶ localizationFunctor.obj A :=
    localizationFunctor.map (A.smallChartSpectrumInclusion i)
  let d := domainι (localizationFunctor.obj A) (A.chartDomain i)
  let c := localizationFunctor.mapIso (A.smallChartDomainIso i)
  have hc : c.hom ≫ d = j := by
    change localizationFunctor.map (A.smallChartDomainIso i).hom ≫
      localizationFunctor.map (A.originalDomainInclusion
        (IndexedAffinoidAtlas.OriginalChartDomain.ofChart i)) = _
    rw [← Functor.map_comp, smallChartDomainIso_hom_comp_inclusion]
  let : Mono j := hc ▸ (inferInstance : Mono (c.hom ≫ d))
  let φ := (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} R T).symm (j ≫ e.hom)
  have hφ : SmallAffinoidSpectrum.localizedMapEquiv.{u, u} R T φ = j ≫ e.hom :=
    Equiv.apply_symm_apply _ _
  let U := range (BanachSpectrum.comap φ.toBoundedRingHom)
  refine ⟨T, φ, U, isCompact_range
    (BanachSpectrum.comapContinuous φ.toBoundedRingHom).continuous |>.isClosed, rfl, ?_⟩
  intro S ψ hψ
  let m := SmallAffinoidSpectrum.localizedMapEquiv.{u, u} R S ψ
  have hm (z : localizedSpaceFunctor.obj (smallSpectrum S)) :
      localizedSpaceFunctor.map (m ≫ e.inv) z ∈ (A.chartDomain i).carrier := by
    obtain ⟨x, rfl⟩ := (SmallAffinoidSpectrum.spectrumHomeomorph.{u, u} S).surjective z
    obtain ⟨y, hy⟩ := hψ x
    let s := SmallAffinoidSpectrum.spectrumHomeomorph.{u, u} S x
    let t := SmallAffinoidSpectrum.spectrumHomeomorph.{u, u} T y
    have he : localizedSpaceFunctor.map m s =
        localizedSpaceFunctor.map (j ≫ e.hom) t := by
      rw [← hφ]
      change (SmallAffinoidSpectrum.map.{u, u} ψ).baseMap s =
        (SmallAffinoidSpectrum.map.{u, u} φ).baseMap t
      exact (SmallAffinoidSpectrum.map_spectrumHomeomorph.{u, u} ψ x).trans
        ((congrArg (SmallAffinoidSpectrum.spectrumHomeomorph.{u, u} R) hy.symm).trans
          (SmallAffinoidSpectrum.map_spectrumHomeomorph.{u, u} φ y).symm)
    have he' : localizedSpaceFunctor.map (m ≫ e.inv) s = localizedSpaceFunctor.map j t := by
      rw [Functor.map_comp, TopCat.comp_app, he, ← TopCat.comp_app, ← Functor.map_comp,
        Category.assoc, e.hom_inv_id, Category.comp_id]
    rw [he']
    exact A.smallChartSpectrumInclusion_mem i t
  obtain ⟨l, hl⟩ := exists_localizedDomainLift (A.chartDomain i) (m ≫ e.inv) hm
  change l ≫ d = m ≫ e.inv at hl
  let n := l ≫ c.inv
  have hn : n ≫ (j ≫ e.hom) = m := by
    dsimp only [n]
    rw [← hc, Category.assoc, ← Category.assoc c.inv, Iso.inv_hom_id_assoc, ← Category.assoc,
      hl, Category.assoc, e.inv_hom_id, Category.comp_id]
  let χ := (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} T S).symm n
  have hχ : SmallAffinoidSpectrum.localizedMapEquiv.{u, u} T S χ = n :=
    Equiv.apply_symm_apply _ _
  refine ⟨χ, ?_, ?_⟩
  · apply (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} R S).injective
    rw [SmallAffinoidSpectrum.localizedMapEquiv_comp.{u, u}, hχ, hφ]
    exact hn
  · intro ξ hξ
    apply (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} T S).injective
    rw [hχ]
    apply (cancel_mono (j ≫ e.hom)).mp
    rw [hn, ← hφ, ← SmallAffinoidSpectrum.localizedMapEquiv_comp.{u, u}, hξ]

theorem affinoidChartDomain_map (e : localizationFunctor.obj A ≅ smallSpectrum R)
    (i : A.presentation.atlas.Index) :
    SmallAffinoidSpectrum.localizedMapEquiv.{u, u} R _ (affinoidChartDomain e i).baseMap =
      localizationFunctor.map (A.smallChartSpectrumInclusion i) ≫ e.hom :=
  Equiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
theorem mem_affinoidChartDomain_iff (e : localizationFunctor.obj A ≅ smallSpectrum R)
    (i : A.presentation.atlas.Index) (x : BanachSpectrum R) :
    x ∈ (affinoidChartDomain e i).locus ↔
      localizedSpaceFunctor.map e.inv (SmallAffinoidSpectrum.spectrumHomeomorph.{u, u} R x) ∈
        range (A.presentation.atlas.chart i) := by
  let D := affinoidChartDomain e i
  let j := localizationFunctor.map (A.smallChartSpectrumInclusion i)
  let c := localizationFunctor.mapIso (A.smallChartDomainIso i)
  let ν := domainι (localizationFunctor.obj A) (A.chartDomain i)
  have hc : c.hom ≫ ν = j := by
    change localizationFunctor.map (A.smallChartDomainIso i).hom ≫
      localizationFunctor.map (A.originalDomainInclusion
        (IndexedAffinoidAtlas.OriginalChartDomain.ofChart i)) = _
    rw [← Functor.map_comp, smallChartDomainIso_hom_comp_inclusion]
  have hr : range (localizedSpaceFunctor.map j) = range (A.presentation.atlas.chart i) := by
    have hcr : range (localizedSpaceFunctor.map c.hom) = univ :=
      (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso c)).surjective.range_eq
    have hν : ⇑(localizedSpaceFunctor.map ν) =
        Subtype.val (p := fun x => x ∈ (A.chartDomain i).carrier) :=
      funext (domainι_apply (X := localizationFunctor.obj A) (A.chartDomain i))
    rw [← hc, Functor.map_comp, TopCat.coe_comp, range_comp, hcr, image_univ]
    change range (localizedSpaceFunctor.map ν) = range (A.presentation.atlas.chart i)
    rw [hν, Subtype.range_coe]
    rfl
  let eR := SmallAffinoidSpectrum.spectrumHomeomorph.{u, u} R
  let eD := SmallAffinoidSpectrum.spectrumHomeomorph.{u, u} D.algebra
  have hg : j = SmallAffinoidSpectrum.localizedMapEquiv.{u, u} R _ D.baseMap ≫ e.inv := by
    rw [affinoidChartDomain_map e i, Category.assoc, e.hom_inv_id, Category.comp_id]
  have htest (z : BanachSpectrum D.algebra) :
      localizedSpaceFunctor.map j (eD z) = localizedSpaceFunctor.map e.inv (eR (D.spectrumMap z)) := by
    rw [hg, Functor.map_comp, TopCat.comp_app]
    exact congrArg (localizedSpaceFunctor.map e.inv)
      (SmallAffinoidSpectrum.map_spectrumHomeomorph.{u, u} D.baseMap z)
  rw [← hr, ← D.represents.2.1]
  refine ⟨?_, ?_⟩
  · rintro ⟨z, rfl⟩
    exact ⟨eD z, htest z⟩
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := eD.surjective y
    rw [htest] at hy
    have hmono := (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso e.symm)).injective
    exact ⟨z, eR.injective (hmono hy)⟩

set_option backward.isDefEq.respectTransparency false in
/-- A quasinet of selected charts on a presentation of an affinoid space
has a finite subfamily giving a full-domain cover of its affinoid algebra. -/
theorem exists_finite_cover_of_affinoidChartDomain
    (e : localizationFunctor.obj A ≅ smallSpectrum R) (I : Set A.presentation.atlas.Index)
    (hI : AtlasTopology.LocallyRefines
      (range fun i : I => range (A.presentation.atlas.chart i.val)) {univ}) :
    ∃ (c : Domain.FiniteCover (Domain.whole K R)) (i : Fin c.size → I),
      ∀ k, c.obj k = affinoidChartDomain e (i k).val := by
  classical
  have hq : AtlasTopology.IsQuasinet
      (range fun i : I => range (A.presentation.atlas.chart i.val)) := by
    intro x
    obtain ⟨σ, hσ, hs, hz, hn⟩ := hI univ (mem_singleton _) x (mem_univ x)
    exact ⟨σ, hσ, hs, fun W hW => (hz W hW).2, by simpa only [nhdsWithin_univ] using hn⟩
  let H := (SmallAffinoidSpectrum.spectrumHomeomorph.{u, u} R).trans
    (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso e.symm))
  have hc : IsCompact (univ : Set A.presentation.space) := by
    have hcompact := isCompact_range H.continuous
    rwa [H.surjective.range_eq] at hcompact
  obtain ⟨σ, hσ, hσI, hσcov⟩ := hq.exists_finite_cover_of_isCompact hc
  let := hσ.fintype
  let n := Fintype.card σ
  let τ := (Fintype.equivFin σ).symm
  choose i hi using fun W : σ => hσI W.property
  let D (k : Fin n) := affinoidChartDomain e (i (τ k)).val
  let c : Domain.FiniteCover (Domain.whole K R) :=
    { size := n
      obj := D
      map := fun k => ⟨(D k).baseMap, BoundedAlgHom.comp_id _⟩
      covers := by
        intro x _
        obtain ⟨W, hW, hxW⟩ := hσcov (mem_univ (H x))
        obtain ⟨k, hk⟩ := τ.surjective ⟨W, hW⟩
        refine ⟨k, (mem_affinoidChartDomain_iff e _ x).mpr ?_⟩
        change H x ∈ range (A.presentation.atlas.chart (i (τ k)).val)
        have hEq : range (A.presentation.atlas.chart (i (τ k)).val) = W :=
          (hi (τ k)).trans (congrArg Subtype.val hk)
        rw [hEq]
        exact hxW }
  exact ⟨c, fun k => i (τ k), fun _ => rfl⟩

end Langlands.Analytic.SaturatedAtlasPresentation
