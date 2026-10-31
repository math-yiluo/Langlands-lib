import Langlands.Geometry.Analytic.StrongAtlasMaps
import Langlands.Geometry.Analytic.AtlasSubatlas
import Langlands.Geometry.Analytic.GeneralizedAffinoid.Domain
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Strong quasi-isomorphisms and actual selected-subatlas inclusions -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Original atlas restrictions represent their exact relative domain against
every finite positive-polyradius presented affinoid test. -/
theorem restriction_represents (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j)) :
    PresentedAffinoidAlgebra.Represents K (a.restriction i j h)
      (a.chart j ⁻¹' Set.range (a.chart i)) :=
  ⟨a.isClosed_relativeDomain i j h, a.range_restriction i j h,
    fun R φ hφ => a.restriction_universal i j h R φ hφ⟩

/-- The domain algebra and structural map are the original atlas data. -/
def restrictionDomain (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j)) :
    PresentedAffinoidAlgebra.Domain K (a.algebra j) where
  algebra := a.algebra i
  baseMap := a.restriction i j h
  locus := a.chart j ⁻¹' Set.range (a.chart i)
  represents := a.restriction_represents i j h

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

namespace StrongHom

/-- The image of a source chart in the coordinates of a target chart. -/
def chartImageLocus (f : StrongHom A B) (i : A.atlas.Index) (j : B.atlas.Index) :
    Set (BanachSpectrum (B.atlas.algebra j)) :=
  B.atlas.chart j ⁻¹' (f.baseMap '' Set.range (A.atlas.chart i))

/-- The actual bounded pullback has exactly the prescribed spectrum image. -/
theorem range_pullback (f : StrongHom A B) (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    Set.range (BanachSpectrum.comap (f.pullback i j h).toBoundedRingHom) =
      f.chartImageLocus i j := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨A.atlas.chart i x, ⟨x, rfl⟩, (f.chart_comm i j h x).symm⟩
  · rintro ⟨z, ⟨x, rfl⟩, hx⟩
    refine ⟨x, (B.atlas.isEmbedding_chart j).injective ?_⟩
    exact (f.chart_comm i j h x).trans hx

theorem isCompact_chartImageLocus (f : StrongHom A B)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    IsCompact (f.chartImageLocus i j) := by
  rw [← f.range_pullback i j h]
  exact isCompact_range
    (BanachSpectrum.comapContinuous (f.pullback i j h).toBoundedRingHom).continuous

theorem isClosed_chartImageLocus (f : StrongHom A B)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    IsClosed (f.chartImageLocus i j) :=
  (f.isCompact_chartImageLocus i j h).isClosed

/-- A strong quasi-isomorphism has an ambient homeomorphism and actual
full affinoid-domain representations at every admissible chart pair. -/
def IsQuasiIso (f : StrongHom A B) : Prop :=
  IsHomeomorph f.baseMap ∧
    ∀ i j (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)),
      PresentedAffinoidAlgebra.Represents K (f.pullback i j h) (f.chartImageLocus i j)

namespace IsQuasiIso

variable {f : StrongHom A B} (hf : f.IsQuasiIso)

/-- The local domain uses the source's actual presented algebra and pullback. -/
def localDomain (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    PresentedAffinoidAlgebra.Domain K (B.atlas.algebra j) where
  algebra := A.atlas.algebra i
  baseMap := f.pullback i j h
  locus := f.chartImageLocus i j
  represents := hf.2 i j h

include hf in
/-- Injectivity and the embedding topology follow from the ambient
homeomorphism and the two charts, independently of domain factorization. -/
theorem isEmbedding_pullback (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    IsEmbedding (BanachSpectrum.comap (f.pullback i j h).toBoundedRingHom) := by
  apply (B.atlas.isEmbedding_chart j).of_comp_iff.mp
  have hsquare :
      B.atlas.chart j ∘ BanachSpectrum.comap (f.pullback i j h).toBoundedRingHom =
        f.baseMap ∘ A.atlas.chart i :=
    funext (f.chart_comm i j h)
  rw [hsquare]
  exact hf.1.homeomorph.isEmbedding.comp (A.atlas.isEmbedding_chart i)

/-- Each admissible local spectrum is homeomorphic to the actual image locus. -/
def localHomeomorph (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    BanachSpectrum (A.atlas.algebra i) ≃ₜ f.chartImageLocus i j :=
  (hf.isEmbedding_pullback i j h).toHomeomorph.trans
    (Homeomorph.setCongr (f.range_pullback i j h))

@[simp]
theorem localHomeomorph_apply_coe (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (x : BanachSpectrum (A.atlas.algebra i)) :
    (hf.localHomeomorph i j h x : BanachSpectrum (B.atlas.algebra j)) =
      BanachSpectrum.comap (f.pullback i j h).toBoundedRingHom x := rfl

end IsQuasiIso

theorem isQuasiIso_id (A : AffinoidAtlasPresentation.{u, v, w} K) :
    (StrongHom.id A).IsQuasiIso := by
  refine ⟨IsHomeomorph.id, ?_⟩
  intro i j h
  simpa only [chartImageLocus, StrongHom.id, ContinuousMap.coe_id, Set.image_id] using
    A.atlas.restriction_represents i j (fun x hx => h ⟨x, hx, rfl⟩)

/-- Restrict a strong map to locally refining original source charts,
retaining every original admissible bounded pullback. -/
def restrictSubatlasSource (f : StrongHom A B) (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P) :
    StrongHom (A.subpresentation P hP) B where
  baseMap := f.baseMap
  target_exists i := f.target_exists i.val
  pullback i j h := f.pullback i.val j h
  chart_comm i j h x := f.chart_comm i.val j h x
  restriction_comm i i' j j' hi hj h h' :=
    f.restriction_comm i.val i'.val j j' hi hj h h'

@[simp]
theorem restrictSubatlasSource_baseMap (f : StrongHom A B)
    (P : A.atlas.Index → Prop) (hP : A.atlas.IsLocallyRefiningSelection P) :
    (f.restrictSubatlasSource P hP).baseMap = f.baseMap := rfl

@[simp]
theorem restrictSubatlasSource_pullback (f : StrongHom A B)
    (P : A.atlas.Index → Prop) (hP : A.atlas.IsLocallyRefiningSelection P)
    (i : (A.subpresentation P hP).atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i.val) ⊆ Set.range (B.atlas.chart j)) :
    (f.restrictSubatlasSource P hP).pullback i j h = f.pullback i.val j h := rfl

/-- The same-space source restriction of a quasi-isomorphism is a quasi-isomorphism. -/
theorem IsQuasiIso.restrictSubatlasSource {f : StrongHom A B} (hf : f.IsQuasiIso)
    (P : A.atlas.Index → Prop) (hP : A.atlas.IsLocallyRefiningSelection P) :
    (f.restrictSubatlasSource P hP).IsQuasiIso :=
  ⟨hf.1, fun i j h => hf.2 i.val j h⟩

end StrongHom

variable (A : AffinoidAtlasPresentation.{u, v, w} K)

/-- The full strong inclusion of a locally refining original subatlas. -/
def strongSubatlasInclusion (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P) :
    StrongHom (A.subpresentation P hP) A :=
  (StrongHom.id A).restrictSubatlasSource P hP

@[simp]
theorem strongSubatlasInclusion_baseMap (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P) :
    (A.strongSubatlasInclusion P hP).baseMap = ContinuousMap.id A.space := rfl

/-- Every admissible pair uses the original bounded atlas restriction. -/
@[simp]
theorem strongSubatlasInclusion_pullback (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P)
    (i : (A.subpresentation P hP).atlas.Index) (j : A.atlas.Index)
    (h : (A.strongSubatlasInclusion P hP).baseMap ''
      Set.range ((A.subpresentation P hP).atlas.chart i) ⊆ Set.range (A.atlas.chart j)) :
    (A.strongSubatlasInclusion P hP).pullback i j h =
      A.atlas.restriction i.val j (fun x hx => h ⟨x, hx, rfl⟩) := rfl

/-- The selected pair agrees with the original chosen inclusion's identity. -/
theorem strongSubatlasInclusion_pullback_selected (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P)
    (i : (A.subpresentation P hP).atlas.Index)
    (h : (A.strongSubatlasInclusion P hP).baseMap ''
      Set.range ((A.subpresentation P hP).atlas.chart i) ⊆
        Set.range (A.atlas.chart i.val)) :
    (A.strongSubatlasInclusion P hP).pullback i i.val h =
      (A.subatlasInclusion P hP).pullback i :=
  A.atlas.restriction_id i.val _

/-- No upper cofinality or directedness is needed for this quasi-isomorphism. -/
theorem isQuasiIso_strongSubatlasInclusion (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P) :
    (A.strongSubatlasInclusion P hP).IsQuasiIso :=
  (StrongHom.isQuasiIso_id A).restrictSubatlasSource P hP

end AffinoidAtlasPresentation

end Langlands.Analytic
