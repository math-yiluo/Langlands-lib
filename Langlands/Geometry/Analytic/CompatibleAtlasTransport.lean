import Langlands.Geometry.Analytic.LocalDomainReindexing
import Langlands.Geometry.Analytic.CompatibleStrongQuasiIsomorphisms

/-! # Compatible atlas maps under ambient and index transport -/

noncomputable section

universe u v w z t

namespace Langlands.Analytic.AffinoidAtlasPresentation

open Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Change the space by a homeomorphism and relabel the chart indices, without
changing their bounded algebra data. -/
def transportReindex (A : AffinoidAtlasPresentation.{u, v, w} K)
    {X : Type z} [TopologicalSpace X] (e : A.space ≃ₜ X)
    {I : Type t} (c : I ≃ A.atlas.Index) : AffinoidAtlasPresentation.{u, z, t} K where
  space := TopCat.of X
  atlas := (A.atlas.transport e).reindex c

namespace StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {X Y : Type z} [TopologicalSpace X] [TopologicalSpace Y]
  (eA : A.space ≃ₜ X) (eB : B.space ≃ₜ Y)
  {I J : Type t} (cA : I ≃ A.atlas.Index) (cB : J ≃ B.atlas.Index)

/-- Conjugate only the ambient continuous map. -/
def transportedBaseMap (f : StrongHom A B) : C(X, Y) :=
  ⟨fun x => eB (f.baseMap (eA.symm x)), eB.continuous.comp
    (f.baseMap.continuous.comp eA.symm.continuous)⟩

theorem transportedBaseMap_image_chart (f : StrongHom A B) (i : I) :
    transportedBaseMap eA eB f '' range ((A.transportReindex eA cA).atlas.chart i) =
      eB '' (f.baseMap '' range (A.atlas.chart (cA i))) := by
  ext y
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    refine ⟨f.baseMap (A.atlas.chart (cA i) s), ⟨_, ⟨s, rfl⟩, rfl⟩, ?_⟩
    change eB (f.baseMap (A.atlas.chart (cA i) s)) =
      eB (f.baseMap (eA.symm (eA (A.atlas.chart (cA i) s))))
    rw [eA.symm_apply_apply]
  · rintro ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, rfl⟩
    refine ⟨eA (A.atlas.chart (cA i) s), ⟨s, rfl⟩, ?_⟩
    change eB (f.baseMap (eA.symm (eA (A.atlas.chart (cA i) s)))) = _
    rw [eA.symm_apply_apply]

theorem transportedBaseMap_admissible_iff (f : StrongHom A B) (i : I) (j : J) :
    transportedBaseMap eA eB f '' range ((A.transportReindex eA cA).atlas.chart i) ⊆
        range ((B.transportReindex eB cB).atlas.chart j) ↔
      f.baseMap '' range (A.atlas.chart (cA i)) ⊆ range (B.atlas.chart (cB j)) := by
  rw [transportedBaseMap_image_chart]
  change eB '' (f.baseMap '' range (A.atlas.chart (cA i))) ⊆
      range (B.atlas.transportChart eB (cB j)) ↔ _
  rw [B.atlas.range_transportChart]
  constructor
  · intro h y hy
    obtain ⟨x, hx, hxy⟩ := h ⟨y, hy, rfl⟩
    exact eB.injective hxy ▸ hx
  · exact image_mono

/-- Transports the entire strong map, keeping every admissible bounded pullback. -/
def transportReindex (f : StrongHom A B) :
    StrongHom (A.transportReindex eA cA) (B.transportReindex eB cB) where
  baseMap := transportedBaseMap eA eB f
  target_exists i := by
    obtain ⟨j, hj⟩ := f.target_exists (cA i)
    obtain ⟨j, rfl⟩ := cB.surjective j
    exact ⟨j, (transportedBaseMap_admissible_iff eA eB cA cB f i j).2 hj⟩
  pullback i j h := f.pullback (cA i) (cB j)
    ((transportedBaseMap_admissible_iff eA eB cA cB f i j).1 h)
  chart_comm i j h s := by
    change eB (B.atlas.chart (cB j)
        (BanachSpectrum.comap (f.pullback (cA i) (cB j) _).toBoundedRingHom s)) =
      eB (f.baseMap (eA.symm (eA (A.atlas.chart (cA i) s))))
    rw [eA.symm_apply_apply]
    exact congrArg eB (f.chart_comm (cA i) (cB j)
      ((transportedBaseMap_admissible_iff eA eB cA cB f i j).1 h) s)
  restriction_comm i i' j j' hi hj h h' :=
    f.restriction_comm (cA i) (cA i') (cB j) (cB j')
      (A.atlas.chart_subset_of_transportSubset eA _ _ hi)
      (B.atlas.chart_subset_of_transportSubset eB _ _ hj)
      ((transportedBaseMap_admissible_iff eA eB cA cB f i j).1 h)
      ((transportedBaseMap_admissible_iff eA eB cA cB f i' j').1 h')

@[simp]
theorem transportReindex_baseMap (f : StrongHom A B) (x : X) :
    (f.transportReindex eA eB cA cB).baseMap x = eB (f.baseMap (eA.symm x)) := rfl

theorem transportReindex_chartImageLocus (f : StrongHom A B) (i : I) (j : J) :
    (f.transportReindex eA eB cA cB).chartImageLocus i j =
      f.chartImageLocus (cA i) (cB j) := by
  change (eB ∘ B.atlas.chart (cB j)) ⁻¹'
    (transportedBaseMap eA eB f '' range ((A.transportReindex eA cA).atlas.chart i)) = _
  rw [transportedBaseMap_image_chart, preimage_comp, eB.preimage_image]
  rfl

/-- The full affinoid-test representation is preserved under transport. -/
theorem IsQuasiIso.transportReindex {f : StrongHom A B} (h : f.IsQuasiIso) :
    (f.transportReindex eA eB cA cB).IsQuasiIso := by
  refine ⟨eB.isHomeomorph.comp (h.1.comp eA.symm.isHomeomorph), ?_⟩
  intro i j hij
  let h' := (transportedBaseMap_admissible_iff eA eB cA cB f i j).1 hij
  exact (congrArg (PresentedAffinoidAlgebra.Represents K (f.pullback (cA i) (cB j) h'))
    (transportReindex_chartImageLocus eA eB cA cB f i j)).mpr (h.2 (cA i) (cB j) h')

end StrongHom

namespace CompatibleStrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {X Y : Type z} [TopologicalSpace X] [TopologicalSpace Y]
  (eA : A.space ≃ₜ X) (eB : B.space ≃ₜ Y)
  {I J : Type t} (cA : I ≃ A.atlas.Index) (cB : J ≃ B.atlas.Index)

/-- The all-test coefficient equation gives local compatibility after any
ambient and index transport. -/
def transportReindex (f : CompatibleStrongHom A B) :
    CompatibleStrongHom (A.transportReindex eA cA) (B.transportReindex eB cB) where
  toStrongHom := f.toStrongHom.transportReindex eA eB cA cB
  compatible := (f.toStrongHom.transportReindex eA eB cA cB).hasLocallyCompatiblePullbacks_iff.mpr
    (by
      intro i j k hj hk
      have h := f.coherent (cA i) (cB j) (cB k)
        ((StrongHom.transportedBaseMap_admissible_iff eA eB cA cB _ i j).1 hj)
        ((StrongHom.transportedBaseMap_admissible_iff eA eB cA cB _ i k).1 hk)
      exact (h.transport B.atlas eB).reindex (B.atlas.transport eB) cB)

@[simp]
theorem transportReindex_pullback (f : CompatibleStrongHom A B) (i : I) (j : J)
    (h : (f.transportReindex eA eB cA cB).baseMap ''
      range ((A.transportReindex eA cA).atlas.chart i) ⊆
        range ((B.transportReindex eB cB).atlas.chart j)) :
    (f.transportReindex eA eB cA cB).pullback i j h = f.pullback (cA i) (cB j)
      ((StrongHom.transportedBaseMap_admissible_iff eA eB cA cB _ i j).1 h) := rfl

end CompatibleStrongHom
end Langlands.Analytic.AffinoidAtlasPresentation
