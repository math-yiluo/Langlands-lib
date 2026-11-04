import Langlands.Geometry.Analytic.SaturatedChartCoverRefinement
import Langlands.Geometry.Analytic.AtlasMapChartChangeNaturality

/-! # Strong pullbacks and chart change on saturated source atlases -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- The ambient image condition needed to change any admissible pullback to
another admissible original target chart. -/
theorem pullback_image_chart (f : StrongHom A B) (i : A.atlas.Index)
    (j k : B.atlas.Index)
    (hj : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hk : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart k))
    (x : BanachSpectrum (A.atlas.algebra i)) :
    B.atlas.chart j (BanachSpectrum.comap (f.pullback i j hj).toBoundedRingHom x) ∈
      Set.range (B.atlas.chart k) := by
  rw [f.chart_comm]
  exact hk ⟨A.atlas.chart i x, ⟨x, rfl⟩, rfl⟩

/-- Construct a new pullback from a single admissible pullback by actual
finite-cover bounded chart change, without using the supplied new pullback. -/
def changeTargetPullback (f : StrongHom A B) (i : A.atlas.Index)
    (j k : B.atlas.Index)
    (hj : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hk : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart k)) :
    BoundedAlgHom K (B.atlas.algebra k) (A.atlas.algebra i) :=
  B.atlas.changeMapChart j k (A.atlas.algebra i) (f.pullback i j hj)
    (f.pullback_image_chart i j k hj hk)

/-- Source saturation allows every inverse-image domain in the chart-change
cover to be replaced by an original source chart. Original strong naturality
then recovers the complete supplied bounded pullback. -/
theorem pullback_eq_changeTargetPullback (f : StrongHom A B)
    (ha : A.atlas.HasAllLocalDomains) (i : A.atlas.Index)
    (j k : B.atlas.Index)
    (hj : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hk : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart k)) :
    f.pullback i k hk = f.changeTargetPullback i j k hj hk := by
  let φ := f.pullback i j hj
  let c := B.atlas.mapImageChartCover j k (A.atlas.algebra i) φ
    (f.pullback_image_chart i j k hj hk)
  let hφ : ∀ x : BanachSpectrum (A.atlas.algebra i),
      B.atlas.chart j (BanachSpectrum.comap φ.toBoundedRingHom x) ∈
        B.atlas.mapChartImage j (A.atlas.algebra i) φ := fun x => ⟨x, rfl⟩
  let d := c.mapPullbackCover (A.atlas.algebra i) φ hφ
  have hlocal (t : Fin c.size) :
      ((ha.chartCover d).map t).restriction.comp (f.pullback i k hk) =
        ((ha.chartCover d).map t).restriction.comp
          (c.glueMapChartChange (A.atlas.algebra i) φ hφ) := by
    let D := B.atlas.restrictionDomain (c.index t) j (c.left_subset t)
    let Q := Domain.pullback φ D
    let m := ha.domainChartIndex i Q
    let hmi := ha.domainChartIndex_subset i Q
    let ρ : BoundedAlgHom K Q.algebra (A.atlas.algebra m) :=
      (ha.chartDomainIso i Q).inv.restriction
    have hρ : ρ.comp Q.baseMap = A.atlas.restriction m i hmi :=
      ha.chartDomainIso_inv_comp_baseMap i Q
    let β : BoundedAlgHom K (B.atlas.algebra (c.index t)) (A.atlas.algebra m) :=
      ρ.comp (Domain.pullbackMap φ D)
    have hβj : β.comp (B.atlas.restriction (c.index t) j (c.left_subset t)) =
        (A.atlas.restriction m i hmi).comp φ := by
      have hs : (Domain.pullbackMap φ D).comp
          (B.atlas.restriction (c.index t) j (c.left_subset t)) =
          Q.baseMap.comp φ := Domain.pullbackMap_comp_baseMap φ D
      calc
        β.comp (B.atlas.restriction (c.index t) j (c.left_subset t)) =
            ρ.comp (Q.baseMap.comp φ) :=
          congrArg (fun q : BoundedAlgHom K (B.atlas.algebra j) Q.algebra =>
            ρ.comp q) hs
        _ = (A.atlas.restriction m i hmi).comp φ :=
          congrArg (fun q : BoundedAlgHom K (A.atlas.algebra i)
            (A.atlas.algebra m) => q.comp φ) hρ
    have hmt : f.baseMap '' Set.range (A.atlas.chart m) ⊆
        Set.range (B.atlas.chart (c.index t)) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [ha.range_domainChartIndex i Q] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      change B.atlas.chart j (BanachSpectrum.comap φ.toBoundedRingHom y) ∈
        Set.range (B.atlas.chart (c.index t)) at hy
      exact (f.chart_comm i j hj y) ▸ hy
    have hmk : f.baseMap '' Set.range (A.atlas.chart m) ⊆
        Set.range (B.atlas.chart k) := (Set.image_mono hmi).trans hk
    have hfm : f.pullback m (c.index t) hmt = β := by
      apply B.atlas.restriction_hom_ext (c.index t) j (c.left_subset t)
        (A.atlas.algebra m)
      exact (f.restriction_comm m i (c.index t) j hmi (c.left_subset t)
        hmt hj).symm.trans hβj.symm
    have hmap : ((ha.chartCover d).map t).restriction =
        A.atlas.restriction m i hmi := hρ
    rw [hmap]
    calc
      (A.atlas.restriction m i hmi).comp (f.pullback i k hk) =
          f.pullback m k hmk := by
        simpa only [B.atlas.restriction_id, BoundedAlgHom.comp_id] using
          f.restriction_comm m i k k hmi Subset.rfl hmk hk
      _ = (f.pullback m (c.index t) hmt).comp
          (B.atlas.restriction (c.index t) k (c.right_subset t)) :=
        f.pullback_comp_restriction m (c.index t) k (c.right_subset t) hmt hmk
      _ = β.comp (B.atlas.restriction (c.index t) k (c.right_subset t)) :=
        congrArg (fun q : BoundedAlgHom K (B.atlas.algebra (c.index t))
          (A.atlas.algebra m) =>
            q.comp (B.atlas.restriction (c.index t) k (c.right_subset t))) hfm
      _ = ρ.comp (c.mapPullbackFamily (A.atlas.algebra i) φ hφ t) := rfl
      _ = (ρ.comp Q.baseMap).comp
          (c.glueMapChartChange (A.atlas.algebra i) φ hφ) :=
        congrArg (fun q : BoundedAlgHom K (B.atlas.algebra k) Q.algebra =>
          ρ.comp q) (c.glueMapChartChange_local (A.atlas.algebra i) φ hφ t).symm
      _ = (A.atlas.restriction m i hmi).comp
          (c.glueMapChartChange (A.atlas.algebra i) φ hφ) :=
        congrArg (fun q : BoundedAlgHom K (A.atlas.algebra i)
          (A.atlas.algebra m) =>
            q.comp (c.glueMapChartChange (A.atlas.algebra i) φ hφ)) hρ
  apply BoundedAlgHom.ext
  intro b
  apply (ha.chartCover d).algebra_ext_of_restrict_eq
  intro t
  exact congrArg (fun q : BoundedAlgHom K (B.atlas.algebra k)
    ((ha.chartCover d).obj t).algebra => q b) (hlocal t)

/-- The supplied strong pullbacks obey the full arbitrary-affinoid-test
chart-change law when the source atlas has all local domains. -/
theorem pullback_isMapChartChange (f : StrongHom A B)
    (ha : A.atlas.HasAllLocalDomains) (i : A.atlas.Index)
    (j k : B.atlas.Index)
    (hj : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hk : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart k)) :
    B.atlas.IsMapChartChange j k (A.atlas.algebra i)
      (f.pullback i j hj) (f.pullback i k hk) := by
  rw [f.pullback_eq_changeTargetPullback ha i j k hj hk]
  exact B.atlas.changeMapChart_isMapChartChange j k (A.atlas.algebra i) _
    (f.pullback_image_chart i j k hj hk)

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
