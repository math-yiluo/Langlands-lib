import Langlands.Geometry.Analytic.FibreProductSmallProjections
import Langlands.Geometry.Analytic.SaturatedLocalDomainPullbackComparison
import Langlands.Geometry.Analytic.LocalDomainSaturatedTransport

/-! # Entire second-projection coefficients on transported actual domains -/

noncomputable section

universe u v

namespace Langlands.Analytic.FibreProduct

open CategoryTheory Set Topology PresentedAffinoidAlgebra AffinoidAtlasPresentation IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, v} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)
  [Small.{v} (chartSystem f g).Space]
  (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
  (hC : C.atlas.HasAllLocalDomains)

/-- Canonical shrinking leaves the entire second image of a locus unchanged. -/
theorem smallSndBase_image_shrink {S : Set (chartSystem f g).Space}
    {T : Set B.space} (h : snd f g '' S ⊆ T) :
    smallSndBase f g hA hB hC '' (Shrink.homeomorph (chartSystem f g).Space) '' S ⊆ T := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  change snd f g ((Shrink.homeomorph (chartSystem f g).Space).symm
    ((Shrink.homeomorph (chartSystem f g).Space) x)) ∈ T
  rw [Homeomorph.symm_apply_apply]
  exact h ⟨x, hx, rfl⟩

/-- A full factor coefficient chart-change law determines the actual
small second projection on any transported original local full domain. -/
theorem smallSnd_localChartPullback_of_factor_change
    (U : LocalDomain (localAtlas f g hA hB hC)) (j : B.atlas.Index)
    (φ : BoundedAlgHom K (B.atlas.algebra j) U.algebra)
    (h : snd f g '' U.locus ⊆ range (B.atlas.chart j))
    (hφ : B.atlas.IsMapChartChange U.index.rep.1.2 j U.algebra
      (U.domain.baseMap.comp (rightMap f g U.index.rep)) φ) :
    let a := localAtlas f g hA hB hC
    let e := Shrink.homeomorph (chartSystem f g).Space
    let c := (equivShrink (LocalAtlasIndex f g)).symm
    let L := (LocalDomain.transportReindexFunctor a e c).obj U
    (smallSndHom f g hA hB hC).toStrongHom.localChartPullback L j
      ((image_mono (LocalDomain.transportReindex_locus a e c U).subset).trans
        (smallSndBase_image_shrink f g hA hB hC h)) =
      (LocalDomain.transportReindexEquiv a e c U).toBoundedAlgHom.comp φ := by
  let a := localAtlas f g hA hB hC
  let e := Shrink.homeomorph (chartSystem f g).Space
  let c := (equivShrink (LocalAtlasIndex f g)).symm
  let b := a.transport e
  let q := smallSndHom f g hA hB hC
  obtain ⟨i, D⟩ := U
  obtain ⟨k, rfl⟩ := c.surjective i
  let U : LocalDomain a := ⟨c k, D⟩
  let W := LocalDomain.transport a e U
  let L := (LocalDomain.transportReindexFunctor a e c).obj U
  let N : LocalDomain (smallAtlas f g hA hB hC) := ⟨k, D⟩
  let r : L ⟶ N := LocalDomain.preimageOfReindex b c
    ((LocalDomain.reindexEquivalence b c).counitIso.app W).hom
  have hr : r.restriction = (LocalDomain.transportReindexEquiv a e c U).toBoundedAlgHom := rfl
  have hN : q.baseMap '' N.locus ⊆ range (B.atlas.chart j) := by
    have he : N.locus = e '' U.locus := LocalDomain.transport_locus a e U
    exact (image_mono he.subset).trans (smallSndBase_image_shrink f g hA hB hC h)
  have hL : q.baseMap '' L.locus ⊆ range (B.atlas.chart j) :=
    (image_mono (LocalDomain.transportReindex_locus a e c U).subset).trans
      (smallSndBase_image_shrink f g hA hB hC h)
  have hk : q.baseMap '' range ((smallAtlas f g hA hB hC).chart k) ⊆
      range (B.atlas.chart (c k).rep.1.2) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact (smallSndBase_chart f g hA hB hC k x).symm ▸ ⟨_, rfl⟩
  have hq : q.pullback k (c k).rep.1.2 hk = rightMap f g (c k).rep :=
    B.atlas.changeMapChart_self _ _ _ _
  have hφ' : B.atlas.IsMapChartChange (c k).rep.1.2 j N.algebra
      (N.domain.baseMap.comp (q.pullback k (c k).rep.1.2 hk)) φ :=
    (congrArg (fun z => N.domain.baseMap.comp z) hq).symm ▸ hφ
  have hcan : q.toStrongHom.localChartPullback N j hN = φ :=
    (q.toStrongHom.localChartPullback_eq_of_parent_chart_change q.coherent N j (c k).rep.1.2
      hk hN φ hφ').symm
  exact (q.toStrongHom.localChartPullback_source q.coherent r j hL hN).symm.trans
    ((congrArg (fun z : BoundedAlgHom K (B.atlas.algebra j) N.algebra => r.restriction.comp z)
      hcan).trans (congrArg (fun z => z.comp φ) hr))

/-- A complete factor coefficient law also determines the original
full-domain factorization of the actual small second projection. -/
theorem smallSnd_localDomainPullback_of_factor_change
    (U : LocalDomain (localAtlas f g hA hB hC)) (V : LocalDomain B.atlas)
    (φ : BoundedAlgHom K V.algebra U.algebra)
    (h : snd f g '' U.locus ⊆ V.locus)
    (hφ : B.atlas.IsMapChartChange U.index.rep.1.2 V.index U.algebra
      (U.domain.baseMap.comp (rightMap f g U.index.rep)) (φ.comp V.domain.baseMap)) :
    let a := localAtlas f g hA hB hC
    let e := Shrink.homeomorph (chartSystem f g).Space
    let c := (equivShrink (LocalAtlasIndex f g)).symm
    let L := (LocalDomain.transportReindexFunctor a e c).obj U
    (smallSndHom f g hA hB hC).toStrongHom.localDomainPullback L V
      ((image_mono (LocalDomain.transportReindex_locus a e c U).subset).trans
        (smallSndBase_image_shrink f g hA hB hC h)) =
      (LocalDomain.transportReindexEquiv a e c U).toBoundedAlgHom.comp φ := by
  let a := localAtlas f g hA hB hC
  let e := Shrink.homeomorph (chartSystem f g).Space
  let c := (equivShrink (LocalAtlasIndex f g)).symm
  let L := (LocalDomain.transportReindexFunctor a e c).obj U
  let q := smallSndHom f g hA hB hC
  let E := LocalDomain.transportReindexEquiv a e c U
  have hL : q.baseMap '' L.locus ⊆ V.locus :=
    (image_mono (LocalDomain.transportReindex_locus a e c U).subset).trans
      (smallSndBase_image_shrink f g hA hB hC h)
  have hp : snd f g '' U.locus ⊆ range (B.atlas.chart V.index) :=
    h.trans (B.atlas.domainSubset_chart V.index V.index V.domain V.domain Subset.rfl)
  have hc := smallSnd_localChartPullback_of_factor_change f g hA hB hC U V.index
    (φ.comp V.domain.baseMap) hp hφ
  exact (q.toStrongHom.localDomainPullback_unique L V hL (E.toBoundedAlgHom.comp φ)
    ((BoundedAlgHom.comp_assoc _ _ _).trans hc.symm)).symm

/-- The complete actual saturation projection retains every supplied
original local-domain coefficient map through both bounded comparisons. -/
theorem smallSnd_saturation_pullback_of_factor_change
    (U : LocalDomain (localAtlas f g hA hB hC)) (V : LocalDomain B.atlas)
    (φ : BoundedAlgHom K V.algebra U.algebra)
    (h : snd f g '' U.locus ⊆ V.locus)
    (hφ : B.atlas.IsMapChartChange U.index.rep.1.2 V.index U.algebra
      (U.domain.baseMap.comp (rightMap f g U.index.rep)) (φ.comp V.domain.baseMap)) :
    let a := localAtlas f g hA hB hC
    let e := Shrink.homeomorph (chartSystem f g).Space
    let c := (equivShrink (LocalAtlasIndex f g)).symm
    let q := smallSndHom f g hA hB hC
    ((q.saturationExtension).pullback (LocalDomain.transportedSaturatedIndex a e c U)
      ⟨V.locus, ⟨V, rfl⟩⟩ (by
        change q.baseMap '' range ((smallAtlas f g hA hB hC).saturatedAtlas.chart _) ⊆
          range (B.atlas.saturatedAtlas.chart _)
        exact (image_mono (LocalDomain.range_transportedSaturatedIndex a e c U).subset).trans
          ((smallSndBase_image_shrink f g hA hB hC h).trans
            (B.atlas.range_saturatedChart ⟨V.locus, ⟨V, rfl⟩⟩).symm.subset))).comp
        (B.atlas.localDomainSaturatedEquiv V).toBoundedAlgHom =
      (LocalDomain.transportedSaturatedEquiv a e c U).toBoundedAlgHom.comp φ := by
  let a := localAtlas f g hA hB hC
  let e := Shrink.homeomorph (chartSystem f g).Space
  let c := (equivShrink (LocalAtlasIndex f g)).symm
  let L := (LocalDomain.transportReindexFunctor a e c).obj U
  let q := smallSndHom f g hA hB hC
  have hL : q.baseMap '' L.locus ⊆ V.locus :=
    (image_mono (LocalDomain.transportReindex_locus a e c U).subset).trans
      (smallSndBase_image_shrink f g hA hB hC h)
  have hn := q.toStrongHom.saturationExtension_pullback_localDomains q.coherent L V hL
  have hc := smallSnd_localDomainPullback_of_factor_change f g hA hB hC U V φ h hφ
  exact hn.trans ((congrArg (fun z : BoundedAlgHom K V.algebra L.algebra =>
    ((smallAtlas f g hA hB hC).localDomainSaturatedEquiv L).toBoundedAlgHom.comp z) hc).trans
      (BoundedAlgHom.comp_assoc _ _ _).symm)

/-- Reexpress the actual small second projection's full-domain pullback
on the unchanged original source algebra, through the bounded counit. -/
def smallSndDomainPullback
    (U : LocalDomain (localAtlas f g hA hB hC)) (V : LocalDomain B.atlas)
    (h : snd f g '' U.locus ⊆ V.locus) : BoundedAlgHom K V.algebra U.algebra :=
  let a := localAtlas f g hA hB hC
  let e := Shrink.homeomorph (chartSystem f g).Space
  let c := (equivShrink (LocalAtlasIndex f g)).symm
  let L := (LocalDomain.transportReindexFunctor a e c).obj U
  (LocalDomain.transportReindexEquiv a e c U).symm.toBoundedAlgHom.comp
    ((smallSndHom f g hA hB hC).toStrongHom.localDomainPullback L V
      ((image_mono (LocalDomain.transportReindex_locus a e c U).subset).trans
        (smallSndBase_image_shrink f g hA hB hC h)))

/-- Certification of the reexpressed complete actual projection map uses
the whole factor coefficient law and full-domain uniqueness. -/
theorem smallSndDomainPullback_eq_of_factor_change
    (U : LocalDomain (localAtlas f g hA hB hC)) (V : LocalDomain B.atlas)
    (φ : BoundedAlgHom K V.algebra U.algebra)
    (h : snd f g '' U.locus ⊆ V.locus)
    (hφ : B.atlas.IsMapChartChange U.index.rep.1.2 V.index U.algebra
      (U.domain.baseMap.comp (rightMap f g U.index.rep)) (φ.comp V.domain.baseMap)) :
    smallSndDomainPullback f g hA hB hC U V h = φ := by
  let a := localAtlas f g hA hB hC
  let e := Shrink.homeomorph (chartSystem f g).Space
  let c := (equivShrink (LocalAtlasIndex f g)).symm
  let L := (LocalDomain.transportReindexFunctor a e c).obj U
  let E := LocalDomain.transportReindexEquiv a e c U
  have hc := smallSnd_localDomainPullback_of_factor_change f g hA hB hC U V φ h hφ
  apply BoundedAlgHom.ext
  intro x
  exact (congrArg (fun z : BoundedAlgHom K V.algebra L.algebra => E.symm (z x)) hc).trans
    (E.symm_apply_apply (φ x))

end Langlands.Analytic.FibreProduct
