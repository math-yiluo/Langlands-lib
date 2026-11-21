import Langlands.Geometry.Analytic.GroundFieldExtensionAtlas
import Langlands.Geometry.Analytic.AtlasReindexing
import Langlands.Geometry.Analytic.AtlasHomeomorph

/-! # Reindexing the actual quotient for ground field extension -/

noncomputable section

universe u v w u' z

namespace Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension

open Set Topology

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)
  {J : Type z} (e : J ≃ a.Index)

/-- The old and renamed chart gluings use the very same common-subchart relation. -/
theorem glued_reindex_iff (i j : J) (s : BanachSpectrum (chartAlgebra K L a (e i)))
    (t : BanachSpectrum (chartAlgebra K L a (e j))) :
    (chartSystem K L (a.reindex e)).Glued i s j t ↔
      (chartSystem K L a).Glued (e i) s (e j) t := by
  constructor
  · rintro ⟨k, hki, hkj, r, hri, hrj⟩
    exact ⟨e k, hki, hkj, r, hri, hrj⟩
  · rintro ⟨k, hki, hkj, r, hri, hrj⟩
    obtain ⟨k, rfl⟩ := e.surjective k
    exact ⟨k, hki, hkj, r, hri, hrj⟩

/-- Quotient descent of the unchanged spectrum point at the renamed index. -/
def reindexPointMap : (chartSystem K L (a.reindex e)).Space → (chartSystem K L a).Space :=
  Quotient.lift (fun p => (chartSystem K L a).chart (e p.1) p.2) (by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    exact (chartSystem K L a).chart_eq_iff.mpr ((glued_reindex_iff K L a e i j s t).mp h))

@[simp]
theorem reindexPointMap_chart (i : J) (s : BanachSpectrum (chartAlgebra K L a (e i))) :
    reindexPointMap K L a e ((chartSystem K L (a.reindex e)).chart i s) =
      (chartSystem K L a).chart (e i) s := rfl

/-- Reindexing may change the universe of the glued space, but not its
quotient topology or its given point on an original chart. -/
def reindexHomeomorph :
    (chartSystem K L (a.reindex e)).Space ≃ₜ (chartSystem K L a).Space := by
  let C := chartSystem K L a
  let D := chartSystem K L (a.reindex e)
  let f := reindexPointMap K L a e
  have hf : Continuous f := by
    apply Continuous.quotient_lift
    exact continuous_sigma fun i => C.continuous_chart (e i)
  have hbij : Function.Bijective f := by
    constructor
    · intro x y hxy
      obtain ⟨i, s, rfl⟩ := D.exists_chart x
      obtain ⟨j, t, rfl⟩ := D.exists_chart y
      exact D.chart_eq_iff.mpr ((glued_reindex_iff K L a e i j s t).mpr (C.chart_eq_iff.mp hxy))
    · intro x
      obtain ⟨j, s, rfl⟩ := C.exists_chart x
      obtain ⟨i, rfl⟩ := e.surjective j
      exact ⟨D.chart i s, rfl⟩
  let g := Equiv.ofBijective f hbij
  have hg : Continuous g.symm := by
    have hq : IsQuotientMap (Quotient.mk' (s := C.setoid)) :=
      isQuotientMap_quotient_mk'
    apply hq.continuous_iff.mpr
    apply continuous_sigma
    intro j
    obtain ⟨i, rfl⟩ := e.surjective j
    have he : g.symm ∘ C.chart (e i) = D.chart i := by
      funext s
      apply g.injective
      exact g.apply_symm_apply (C.chart (e i) s)
    change Continuous (g.symm ∘ C.chart (e i))
    rw [he]
    exact D.continuous_chart i
  exact ⟨g, hf, hg⟩

@[simp]
theorem reindexHomeomorph_chart (i : J) (s : BanachSpectrum (chartAlgebra K L a (e i))) :
    reindexHomeomorph K L a e ((chartSystem K L (a.reindex e)).chart i s) =
      (chartSystem K L a).chart (e i) s := rfl

@[simp]
theorem reindexHomeomorph_symm_chart (i : J) (s : BanachSpectrum (chartAlgebra K L a (e i))) :
    (reindexHomeomorph K L a e).symm ((chartSystem K L a).chart (e i) s) =
      (chartSystem K L (a.reindex e)).chart i s :=
  (reindexHomeomorph K L a e).symm_apply_apply ((chartSystem K L (a.reindex e)).chart i s)

/-- On projecting to the ground field, the homeomorphism just forgets the new label. -/
theorem projection_reindexHomeomorph (x : (chartSystem K L (a.reindex e)).Space) :
    projection K L a (reindexHomeomorph K L a e x) = projection K L (a.reindex e) x := by
  obtain ⟨i, s, rfl⟩ := (chartSystem K L (a.reindex e)).exists_chart x
  rfl

/-- All bounded restrictions, as well as chart domains, are retained by the
homeomorphism. Transport the reindexed gluing to the original quotient space. -/
theorem transport_atlas_reindex :
    (atlas K L (a.reindex e)).transport (reindexHomeomorph K L a e) =
      (atlas K L a).reindex e := rfl

end Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension
