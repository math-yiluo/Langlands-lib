import Langlands.Geometry.Analytic.AtlasMapChartChangeLocality
import Langlands.Geometry.Analytic.CoherentStrongSaturationUniqueness

/-! # Strong atlas maps with explicit local affinoid compatibility -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

namespace StrongHom

/-- Compatibility of the supplied original family is the bounded equation
on each actual inverse-image domain of every common original target chart. -/
def HasLocallyCompatiblePullbacks (f : StrongHom A B) : Prop :=
  ∀ (i : A.atlas.Index) (j k : B.atlas.Index)
    (hj : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hk : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart k)),
    B.atlas.IsLocalMapChartChange j k (A.atlas.algebra i)
      (f.pullback i j hj) (f.pullback i k hk)

/-- Actual local-domain compatibility and all-coefficient coherence are
equivalent laws on the original bounded maps. -/
theorem hasLocallyCompatiblePullbacks_iff (f : StrongHom A B) :
    f.HasLocallyCompatiblePullbacks ↔ f.HasCoherentPullbacks := by
  constructor
  · intro h i j k hj hk
    exact (B.atlas.isMapChartChange_iff_local j k _ _ _).mpr (h i j k hj hk)
  · intro h i j k hj hk
    exact (B.atlas.isMapChartChange_iff_local j k _ _ _).mp (h i j k hj hk)

/-- Restriction from any original source chart to any actual local domain
recovers the constructed bounded local map. -/
theorem original_pullback_restrict (f : StrongHom A B) (hf : f.HasCoherentPullbacks)
    (W : LocalDomain A.atlas) (i : A.atlas.Index)
    (p : W ⟶ A.atlas.originalLocalDomain i) (j : B.atlas.Index)
    (hj : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hW : f.baseMap '' W.locus ⊆ Set.range (B.atlas.chart j)) :
    p.restriction.comp (f.pullback i j hj) = f.localChartPullback W j hW := by
  have hp := f.localChartPullback_source hf p j hW (by
    rw [A.atlas.originalLocalDomain_locus]
    exact hj)
  rw [f.localChartPullback_of_parent_admissible hf (A.atlas.originalLocalDomain i)
    j hj _] at hp
  have hid : (A.atlas.originalLocalDomain i).domain.baseMap.comp (f.pullback i j hj) =
      f.pullback i j hj := BoundedAlgHom.id_comp _
  exact (congrArg (fun r : BoundedAlgHom K (B.atlas.algebra j) (A.atlas.algebra i) =>
    p.restriction.comp r) hid).symm.trans hp

/-- Original maps from different source charts agree on every actual common
local source domain, through actual inverse-image domains of common target
subcharts. No comparable source parents are required. -/
theorem original_pullbacks_local_overlap (f : StrongHom A B)
    (hf : f.HasLocallyCompatiblePullbacks)
    (W : LocalDomain A.atlas) (i i' : A.atlas.Index)
    (p : W ⟶ A.atlas.originalLocalDomain i)
    (q : W ⟶ A.atlas.originalLocalDomain i') (j k : B.atlas.Index)
    (hj : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hk : f.baseMap '' Set.range (A.atlas.chart i') ⊆ Set.range (B.atlas.chart k)) :
    B.atlas.IsLocalMapChartChange j k W.algebra
      (p.restriction.comp (f.pullback i j hj))
      (q.restriction.comp (f.pullback i' k hk)) := by
  have hc := f.hasLocallyCompatiblePullbacks_iff.mp hf
  have hp : f.baseMap '' W.locus ⊆ Set.range (B.atlas.chart j) := by
    have h := p.subset
    rw [A.atlas.originalLocalDomain_locus] at h
    exact (Set.image_mono h).trans hj
  have hq : f.baseMap '' W.locus ⊆ Set.range (B.atlas.chart k) := by
    have h := q.subset
    rw [A.atlas.originalLocalDomain_locus] at h
    exact (Set.image_mono h).trans hk
  rw [f.original_pullback_restrict hc W i p j hj hp,
    f.original_pullback_restrict hc W i' q k hk hq]
  exact (B.atlas.isMapChartChange_iff_local j k _ _ _).mp
    (f.localChartPullback_isMapChartChange W j k hp hq)

end StrongHom

/-- Actual continuous and all-admissible bounded strong-map data, with the
explicit local compatibility of the original affinoid morphisms. -/
structure CompatibleStrongHom (A B : AffinoidAtlasPresentation.{u, v, w} K)
    extends StrongHom A B where
  compatible : toStrongHom.HasLocallyCompatiblePullbacks

namespace CompatibleStrongHom

theorem coherent (f : CompatibleStrongHom A B) : f.toStrongHom.HasCoherentPullbacks :=
  f.toStrongHom.hasLocallyCompatiblePullbacks_iff.mp f.compatible

@[ext]
theorem ext {f g : CompatibleStrongHom A B}
    (h : f.toStrongHom = g.toStrongHom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Identities use the actual original atlas restrictions. -/
def id (A : AffinoidAtlasPresentation.{u, v, w} K) : CompatibleStrongHom A A where
  toStrongHom := StrongHom.id A
  compatible := (StrongHom.id A).hasLocallyCompatiblePullbacks_iff.mpr
    (StrongHom.hasCoherentPullbacks_id A)

/-- For a saturated source, the original restriction equations already
discharge the explicit local compatibility law. -/
def ofSaturated (f : StrongHom A B) (ha : A.atlas.HasAllLocalDomains) :
    CompatibleStrongHom A B where
  toStrongHom := f
  compatible := f.hasLocallyCompatiblePullbacks_iff.mpr
    (f.hasCoherentPullbacks_of_saturated ha)

/-- Construct the actual extension to both enlarged atlases. The input law
concerns only original maps and their actual inverse-image source domains. -/
def saturationExtension (f : CompatibleStrongHom A B) :
    StrongHom A.saturatedPresentation B.saturatedPresentation :=
  f.toStrongHom.saturationExtension f.coherent

@[simp]
theorem saturationExtension_baseMap (f : CompatibleStrongHom A B) :
    f.saturationExtension.baseMap = f.baseMap := rfl

theorem saturationExtension_recovers (f : CompatibleStrongHom A B) :
    f.toStrongHom.IsSaturationExtension f.saturationExtension :=
  f.toStrongHom.saturationExtension_isSaturationExtension f.coherent

/-- Complete recovery of all original bounded maps determines the extension
uniquely among all strong maps on the two enlarged atlases. -/
theorem saturationExtension_unique (f : CompatibleStrongHom A B)
    (F : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (hF : f.toStrongHom.IsSaturationExtension F) : F = f.saturationExtension :=
  f.toStrongHom.saturationExtension_unique f.coherent F hF

theorem existsUnique_saturationExtension (f : CompatibleStrongHom A B) :
    ∃! F : StrongHom A.saturatedPresentation B.saturatedPresentation,
      f.toStrongHom.IsSaturationExtension F :=
  f.toStrongHom.existsUnique_saturationExtension f.coherent

end CompatibleStrongHom
end Langlands.Analytic.AffinoidAtlasPresentation
