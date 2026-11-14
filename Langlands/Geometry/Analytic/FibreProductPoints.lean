import Langlands.Geometry.Analytic.AnalyticFibreProduct

/-! # Compatible points of the glued analytic fibre product -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Every point belongs to the range of an atlas chart. -/
theorem exists_chart_at (x : X) : ∃ i, x ∈ range (a.chart i) := by
  have hx : x ∈ ⋃₀ range (fun i => range (a.chart i)) := by
    rw [a.isNet_chartFamily.1.covers]
    trivial
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := mem_sUnion.mp hx
  exact ⟨i, hi⟩

end IndexedAffinoidAtlas

namespace FibreProduct

open AffinoidAtlasPresentation

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)

/-- Compatible factor points belong to a pair of charts having a common base
chart, if both source atlases contain all local domains. -/
theorem exists_pair_of_compatible_points (hA : A.atlas.HasAllLocalDomains)
    (hB : B.atlas.HasAllLocalDomains) (x : A.space) (y : B.space)
    (hxy : f.baseMap x = g.baseMap y) :
    ∃ p : PairIndex f g,
      x ∈ range (A.atlas.chart p.1.1) ∧ y ∈ range (B.atlas.chart p.1.2) := by
  obtain ⟨a, ha⟩ := A.atlas.exists_chart_at x
  obtain ⟨b, hb⟩ := B.atlas.exists_chart_at y
  obtain ⟨k, hk⟩ := f.target_exists a
  obtain ⟨l, hl⟩ := g.target_exists b
  have hxk : f.baseMap x ∈ range (C.atlas.chart k) := hk ⟨x, ha, rfl⟩
  have hxl : f.baseMap x ∈ range (C.atlas.chart l) := by
    rw [hxy]
    exact hl ⟨y, hb, rfl⟩
  obtain ⟨m, hm, hxm⟩ := IndexedAffinoidAtlas.exists_chart_inter hxk hxl
  obtain ⟨c, hc⟩ := exists_chart_preimage hA a hk (hm.trans inter_subset_left)
  obtain ⟨d, hd⟩ := exists_chart_preimage hB b hl (hm.trans inter_subset_right)
  refine ⟨⟨(c, d), m, ⟨?_, ?_⟩⟩, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [hc] at hz
    exact hz.2
  · rintro _ ⟨z, hz, rfl⟩
    rw [hd] at hz
    exact hz.2
  · change x ∈ range (A.atlas.chart c)
    rw [hc]
    exact ⟨ha, hxm⟩
  · change y ∈ range (B.atlas.chart d)
    rw [hd]
    exact ⟨hb, by change g.baseMap y ∈ range (C.atlas.chart m); rwa [← hxy]⟩

/-- Every compatible pair of factor points lifts to the glued fibre-product
chart system. No Hausdorff hypothesis is needed for this point assertion. -/
theorem exists_point (hA : A.atlas.HasAllLocalDomains)
    (hB : B.atlas.HasAllLocalDomains) (x : A.space) (y : B.space)
    (hxy : f.baseMap x = g.baseMap y) :
    ∃ z : (chartSystem f g).Space, fst f g z = x ∧ snd f g z = y := by
  obtain ⟨p, ⟨a, ha⟩, ⟨b, hb⟩⟩ :=
    exists_pair_of_compatible_points f g hA hB x y hxy
  have hab : BanachSpectrum.comap (leftBase f g p).toBoundedRingHom a =
      BanachSpectrum.comap (rightBase f g p).toBoundedRingHom b := by
    apply (C.atlas.isEmbedding_chart (base f g p)).injective
    rw [f.chart_comm, g.chart_comm, ha, hb]
    exact hxy
  obtain ⟨z, hzA, hzB⟩ :=
    AffinoidPushout.exists_point (leftBase f g p) (rightBase f g p) a b hab
  refine ⟨(chartSystem f g).chart p z, ?_, ?_⟩
  · rw [fst_chart]
    exact (congrArg (A.atlas.chart p.1.1) hzA).trans ha
  · rw [snd_chart]
    exact (congrArg (B.atlas.chart p.1.2) hzB).trans hb

/-- A chosen lift of a compatible pair of factor points to the glued chart
system. -/
def pointLift (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (x : A.space) (y : B.space) (hxy : f.baseMap x = g.baseMap y) :
    (chartSystem f g).Space :=
  (exists_point f g hA hB x y hxy).choose

@[simp]
theorem fst_pointLift (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (x : A.space) (y : B.space) (hxy : f.baseMap x = g.baseMap y) :
    fst f g (pointLift f g hA hB x y hxy) = x :=
  (exists_point f g hA hB x y hxy).choose_spec.1

@[simp]
theorem snd_pointLift (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (x : A.space) (y : B.space) (hxy : f.baseMap x = g.baseMap y) :
    snd f g (pointLift f g hA hB x y hxy) = y :=
  (exists_point f g hA hB x y hxy).choose_spec.2

end FibreProduct

namespace SaturatedAtlasPresentation

variable {X Y S : SaturatedAtlasPresentation.{u, u, u} K}
  [T2Space X.presentation.space] [T2Space Y.presentation.space]
  [T2Space S.presentation.space] (f : X ⟶ S) (g : Y ⟶ S)

/-- Compatible points lift to the constructed analytic fibre product. -/
theorem exists_fibreProduct_point (x : X.presentation.space) (y : Y.presentation.space)
    (hxy : f.baseMap x = g.baseMap y) :
    ∃ z : (fibreProduct f g).presentation.space,
      (fibreProductFst f g).baseMap z = x ∧ (fibreProductSnd f g).baseMap z = y :=
  FibreProduct.exists_point (compatibleMap f) (compatibleMap g)
    X.hasAllLocalDomains Y.hasAllLocalDomains x y hxy

end SaturatedAtlasPresentation
end Langlands.Analytic
