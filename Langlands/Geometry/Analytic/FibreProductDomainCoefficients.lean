import Langlands.Geometry.Analytic.FibreProductLocalAtlas
import Langlands.Geometry.Analytic.AtlasDomainMapChartChange
import Langlands.Geometry.Analytic.AtlasDomainCategory

/-! # Full coefficient comparisons for product local domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.FibreProduct

open CategoryTheory Set PresentedAffinoidAlgebra AffinoidAtlasPresentation IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)
  (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
  (hC : C.atlas.HasAllLocalDomains)

/-- Full coefficient chart changes on both original factors determine
the full chart change on the actual local product atlas. -/
theorem localAtlas_isMapChartChange_of_legs
    (p q : LocalAtlasIndex f g) (R : PresentedAffinoidAlgebra K)
    (α : BoundedAlgHom K (algebra f g p.rep) R)
    (β : BoundedAlgHom K (algebra f g q.rep) R)
    (hL : A.atlas.IsMapChartChange p.rep.1.1 q.rep.1.1 R
      (α.comp (leftMap f g p.rep)) (β.comp (leftMap f g q.rep)))
    (hR : B.atlas.IsMapChartChange p.rep.1.2 q.rep.1.2 R
      (α.comp (rightMap f g p.rep)) (β.comp (rightMap f g q.rep))) :
    (localAtlas f g hA hB hC).IsMapChartChange p q R α β := by
  intro T η m hmp hmq θ hθ
  change θ.comp (rangeRestriction f g hmp) = η.comp α at hθ
  apply AffinoidPushout.hom_ext
  · change (η.comp β).comp (leftMap f g q.rep) =
      (θ.comp (rangeRestriction f g hmq)).comp (leftMap f g q.rep)
    have he : θ.comp (rangeLeft f g hmp) = η.comp (α.comp (leftMap f g p.rep)) := by
      calc
        _ = θ.comp ((rangeRestriction f g hmp).comp (leftMap f g p.rep)) :=
          congrArg (fun z => θ.comp z) (rangeRestriction_comp_leftMap f g hmp).symm
        _ = (η.comp α).comp (leftMap f g p.rep) :=
          congrArg (fun z : BoundedAlgHom K (algebra f g p.rep) T =>
            z.comp (leftMap f g p.rep)) hθ
        _ = _ := rfl
    have h₁ := (A.atlas.changeMapChart_isMapChartChange
      m.rep.1.1 p.rep.1.1 (algebra f g m.rep) (leftMap f g m.rep)
        (leftPoint_mem_of_range_subset hmp)).comp A.atlas θ
    change A.atlas.IsMapChartChange m.rep.1.1 p.rep.1.1 T
      (θ.comp (leftMap f g m.rep)) (θ.comp (rangeLeft f g hmp)) at h₁
    rw [he] at h₁
    have h₂ := IndexedAffinoidAtlas.IsMapChartChange.trans A.atlas
      (i := m.rep.1.1) (j := p.rep.1.1) (k := q.rep.1.1) (R := T)
      (φ := θ.comp (leftMap f g m.rep))
      (ψ := η.comp (α.comp (leftMap f g p.rep)))
      (χ := η.comp (β.comp (leftMap f g q.rep)))
      (fun x => leftPoint_mem_of_range_subset hmp
        (BanachSpectrum.comap θ.toBoundedRingHom x)) h₁ (hL.comp A.atlas η)
    have h₃ := (A.atlas.changeMapChart_isMapChartChange
      m.rep.1.1 q.rep.1.1 (algebra f g m.rep) (leftMap f g m.rep)
        (leftPoint_mem_of_range_subset hmq)).comp A.atlas θ
    have heq := (A.atlas.eq_changeMapChart m.rep.1.1 q.rep.1.1 T
      (θ.comp (leftMap f g m.rep))
      (fun x => leftPoint_mem_of_range_subset hmq
        (BanachSpectrum.comap θ.toBoundedRingHom x))
      (η.comp (β.comp (leftMap f g q.rep))) h₂).trans
        (A.atlas.eq_changeMapChart _ _ T _ _ _ h₃).symm
    exact heq.trans (congrArg (fun z => θ.comp z)
      (rangeRestriction_comp_leftMap f g hmq).symm)
  · change (η.comp β).comp (rightMap f g q.rep) =
      (θ.comp (rangeRestriction f g hmq)).comp (rightMap f g q.rep)
    have he : θ.comp (rangeRight f g hmp) = η.comp (α.comp (rightMap f g p.rep)) := by
      calc
        _ = θ.comp ((rangeRestriction f g hmp).comp (rightMap f g p.rep)) :=
          congrArg (fun z => θ.comp z) (rangeRestriction_comp_rightMap f g hmp).symm
        _ = (η.comp α).comp (rightMap f g p.rep) :=
          congrArg (fun z : BoundedAlgHom K (algebra f g p.rep) T =>
            z.comp (rightMap f g p.rep)) hθ
        _ = _ := rfl
    have h₁ := (B.atlas.changeMapChart_isMapChartChange
      m.rep.1.2 p.rep.1.2 (algebra f g m.rep) (rightMap f g m.rep)
        (rightPoint_mem_of_range_subset hmp)).comp B.atlas θ
    change B.atlas.IsMapChartChange m.rep.1.2 p.rep.1.2 T
      (θ.comp (rightMap f g m.rep)) (θ.comp (rangeRight f g hmp)) at h₁
    rw [he] at h₁
    have h₂ := IndexedAffinoidAtlas.IsMapChartChange.trans B.atlas
      (i := m.rep.1.2) (j := p.rep.1.2) (k := q.rep.1.2) (R := T)
      (φ := θ.comp (rightMap f g m.rep))
      (ψ := η.comp (α.comp (rightMap f g p.rep)))
      (χ := η.comp (β.comp (rightMap f g q.rep)))
      (fun x => rightPoint_mem_of_range_subset hmp
        (BanachSpectrum.comap θ.toBoundedRingHom x)) h₁ (hR.comp B.atlas η)
    have h₃ := (B.atlas.changeMapChart_isMapChartChange
      m.rep.1.2 q.rep.1.2 (algebra f g m.rep) (rightMap f g m.rep)
        (rightPoint_mem_of_range_subset hmq)).comp B.atlas θ
    have heq := (B.atlas.eq_changeMapChart m.rep.1.2 q.rep.1.2 T
      (θ.comp (rightMap f g m.rep))
      (fun x => rightPoint_mem_of_range_subset hmq
        (BanachSpectrum.comap θ.toBoundedRingHom x))
      (η.comp (β.comp (rightMap f g q.rep))) h₂).trans
        (B.atlas.eq_changeMapChart _ _ T _ _ _ h₃).symm
    exact heq.trans (congrArg (fun z => θ.comp z)
      (rangeRestriction_comp_rightMap f g hmq).symm)

/-- Factor coefficient laws certify an actual local-domain arrow. The
restriction is the supplied whole bounded map, by full-domain uniqueness. -/
def localDomainInclusionOfLegs
    (U V : LocalDomain (localAtlas f g hA hB hC)) (h : U.locus ⊆ V.locus)
    (φ : BoundedAlgHom K V.algebra U.algebra)
    (hL : A.atlas.IsMapChartChange U.index.rep.1.1 V.index.rep.1.1 U.algebra
      (U.domain.baseMap.comp (leftMap f g U.index.rep))
      ((φ.comp V.domain.baseMap).comp (leftMap f g V.index.rep)))
    (hR : B.atlas.IsMapChartChange U.index.rep.1.2 V.index.rep.1.2 U.algebra
      (U.domain.baseMap.comp (rightMap f g U.index.rep))
      ((φ.comp V.domain.baseMap).comp (rightMap f g V.index.rep))) :
    U ⟶ V := by
  let a := localAtlas f g hA hB hC
  have hc := localAtlas_isMapChartChange_of_legs f g hA hB hC
    U.index V.index U.algebra U.domain.baseMap (φ.comp V.domain.baseMap) hL hR
  have he : φ = (LocalDomain.Inclusion.ofSubset U V h).restriction := by
    apply a.eq_domainRestriction_of_over_base U.index V.index U.domain V.domain h φ
    exact (a.eq_changeMapChart U.index V.index U.algebra U.domain.baseMap
      (a.domainBaseMap_image_chart U.index V.index U.domain
        (a.domainSubset_chart U.index V.index U.domain V.domain h))
      (φ.comp V.domain.baseMap) hc).trans
        (a.domainChartRestriction_eq_changeMapChart U.index V.index U.domain
          (a.domainSubset_chart U.index V.index U.domain V.domain h)).symm
  exact
    { subset := h
      restriction := φ
      comp_chart q hU hV := by
        rw [he]
        exact (LocalDomain.Inclusion.ofSubset U V h).comp_chart q hU hV }

theorem localDomainInclusionOfLegs_restriction
    (U V : LocalDomain (localAtlas f g hA hB hC)) (h : U.locus ⊆ V.locus)
    (φ : BoundedAlgHom K V.algebra U.algebra) (hL) (hR) :
    (localDomainInclusionOfLegs f g hA hB hC U V h φ hL hR).restriction = φ := rfl

end Langlands.Analytic.FibreProduct
