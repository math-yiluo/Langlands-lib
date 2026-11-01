import Langlands.Geometry.Analytic.OriginalDomainStrongPresheaf
import Langlands.Geometry.Analytic.OriginalDomainTopology

/-! # Full strong-map descent for domain families containing every original chart -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.AffinoidAtlasPresentation

open Set CategoryTheory IndexedAffinoidAtlas.OriginalChartDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K} {ι : Type z}

/-- Every original source chart lies wholly inside a member of the family. -/
def OriginalDomainCoversCharts (D : ι → A.atlas.OriginalChartDomain) : Prop :=
  ∀ i : A.atlas.Index, ∃ k, ofChart i ≤ D k

/-- Full strong maps on actual domains, agreeing on their actual intersections.
There is no global map or missing local bounded pullback among these inputs. -/
structure OriginalDomainStrongMatchingFamily (A B : AffinoidAtlasPresentation.{u, v, w} K)
    (D : ι → A.atlas.OriginalChartDomain) where
  localMap : ∀ k, StrongHom (A.originalDomainPresentation (D k)) B
  overlap : ∀ k l,
    (localMap k).restrictOriginalDomain (inf_le_left : D k ⊓ D l ≤ D k) =
      (localMap l).restrictOriginalDomain (inf_le_right : D k ⊓ D l ≤ D l)

namespace OriginalDomainStrongMatchingFamily

variable {D : ι → A.atlas.OriginalChartDomain}

@[ext]
theorem ext {d e : OriginalDomainStrongMatchingFamily A B D}
    (h : d.localMap = e.localMap) : d = e := by
  cases d
  cases e
  cases h
  rfl

/-- Overlap compatibility gives equality on every smaller common domain. -/
theorem restrict_eq (d : OriginalDomainStrongMatchingFamily A B D)
    (k l : ι) {S : A.atlas.OriginalChartDomain} (hSk : S ≤ D k) (hSl : S ≤ D l) :
    (d.localMap k).restrictOriginalDomain hSk =
      (d.localMap l).restrictOriginalDomain hSl := by
  calc
    (d.localMap k).restrictOriginalDomain hSk =
        ((d.localMap k).restrictOriginalDomain
          (inf_le_left : D k ⊓ D l ≤ D k)).restrictOriginalDomain (le_inf hSk hSl) :=
      ((d.localMap k).restrictOriginalDomain_trans (le_inf hSk hSl) inf_le_left).symm
    _ = ((d.localMap l).restrictOriginalDomain
          (inf_le_right : D k ⊓ D l ≤ D l)).restrictOriginalDomain (le_inf hSk hSl) :=
      congrArg (fun f => f.restrictOriginalDomain (le_inf hSk hSl)) (d.overlap k l)
    _ = (d.localMap l).restrictOriginalDomain hSl :=
      (d.localMap l).restrictOriginalDomain_trans (le_inf hSk hSl) inf_le_right

/-- Select a containing family member for each source chart and restrict its
full map. The overlap equations prove the required full chart compatibility. -/
def toStrongChartMapData (d : OriginalDomainStrongMatchingFamily A B D)
    (select : A.atlas.Index → ι) (hselect : ∀ i, ofChart i ≤ D (select i)) :
    StrongChartMapData A B where
  localMap i := (d.localMap (select i)).restrictOriginalDomain (hselect i)
  baseMap_comm i i' hi x :=
    congrArg (fun f : StrongHom (A.chartPresentation i) B => f.baseMap x)
      (d.restrict_eq (select i) (select i') (hselect i) (hi.trans (hselect i')))
  pullback_comm i i' hi j h h' := by
    have hlarge := (StrongHom.restrictOriginalDomain_admissible_iff (A := A)
      (S := ofChart i') (T := D (select i'))
      (hselect i') (d.localMap (select i')) ⟨i, hi⟩ j).mp h'
    have hsmall := (StrongHom.restrictOriginalDomain_admissible_iff (A := A)
      (S := ofChart i) (T := D (select i'))
      (hi.trans (hselect i')) (d.localMap (select i')) (A.chartTopIndex i) j).mpr hlarge
    exact StrongHom.pullback_congr
      (d.restrict_eq (select i) (select i') (hselect i) (hi.trans (hselect i')))
      (A.chartTopIndex i) j h hsmall

/-- Construct a global full strong map using any specified containing members. -/
def glueWith (d : OriginalDomainStrongMatchingFamily A B D)
    (select : A.atlas.Index → ι) (hselect : ∀ i, ofChart i ≤ D (select i)) :
    StrongHom A B :=
  (d.toStrongChartMapData select hselect).toStrongHom

/-- On any chart contained in any family member, the constructed map has the
given local value, regardless of the member chosen for that chart. -/
theorem glueWith_apply_chart (d : OriginalDomainStrongMatchingFamily A B D)
    (select : A.atlas.Index → ι) (hselect : ∀ i, ofChart i ≤ D (select i))
    (k : ι) (i : A.atlas.Index) (hi : ofChart i ≤ D k)
    (x : Set.range (A.atlas.chart i)) :
    (d.glueWith select hselect).baseMap x.val =
      (d.localMap k).baseMap ⟨x.val, hi x.property⟩ :=
  ((d.toStrongChartMapData select hselect).baseMap_apply i x).trans
    (congrArg (fun f : StrongHom (A.chartPresentation i) B => f.baseMap x)
      (d.restrict_eq (select i) k (hselect i) hi))

/-- Recovery of all local point values uses coverage by the contained original
charts of the actual domain, including its entire induced topology. -/
theorem glueWith_apply (d : OriginalDomainStrongMatchingFamily A B D)
    (select : A.atlas.Index → ι) (hselect : ∀ i, ofChart i ≤ D (select i))
    (k : ι) (x : D k) :
    (d.glueWith select hselect).baseMap x.val = (d.localMap k).baseMap x := by
  have hx : x ∈ ⋃₀ Set.range
      (fun c => Set.range ((A.originalDomainPresentation (D k)).atlas.chart c)) := by
    rw [(A.originalDomainPresentation (D k)).atlas.isNet_chartFamily.1.covers]
    trivial
  obtain ⟨_, ⟨c, rfl⟩, y, rfl⟩ := Set.mem_sUnion.mp hx
  exact d.glueWith_apply_chart select hselect k c.val c.property
    ⟨A.atlas.chart c.val y, ⟨y, rfl⟩⟩

/-- The glued map retains every bounded pullback on any member's original chart.
The two admissibility witnesses are independent. -/
theorem glueWith_pullback (d : OriginalDomainStrongMatchingFamily A B D)
    (select : A.atlas.Index → ι) (hselect : ∀ i, ofChart i ≤ D (select i))
    (k : ι) (c : A.atlas.SubspaceChart (D k).carrier) (j : B.atlas.Index)
    (h : (d.glueWith select hselect).baseMap '' Set.range (A.atlas.chart c.val) ⊆
      Set.range (B.atlas.chart j))
    (hk : (d.localMap k).baseMap ''
      Set.range ((A.originalDomainPresentation (D k)).atlas.chart c) ⊆
        Set.range (B.atlas.chart j)) :
    (d.glueWith select hselect).pullback c.val j h =
      (d.localMap k).pullback c j hk :=
  StrongHom.pullback_congr
    (d.restrict_eq (select c.val) k (hselect c.val) c.property)
    (A.chartTopIndex c.val) j
    (((d.toStrongChartMapData select hselect).admissible_iff
      c.val (A.chartTopIndex c.val) j).mp h)
    ((StrongHom.restrictOriginalDomain_admissible_iff (A := A)
      (S := ofChart c.val) (T := D k) c.property (d.localMap k)
      (A.chartTopIndex c.val) j).mpr hk)

/-- Restriction recovers each complete local strong map, including every
admissible bounded algebra pullback. -/
@[simp]
theorem glueWith_restrictSubspace (d : OriginalDomainStrongMatchingFamily A B D)
    (select : A.atlas.Index → ι) (hselect : ∀ i, ofChart i ≤ D (select i)) (k : ι) :
    (d.glueWith select hselect).restrictSubspace (D k).carrier (D k).is_domain =
      d.localMap k := by
  refine StrongHom.ext_of_pullback
    (ContinuousMap.ext (d.glueWith_apply select hselect k)) ?_
  intro c j h h'
  exact d.glueWith_pullback select hselect k c j
    (((d.glueWith select hselect).restrictSubspace_admissible_iff
      (D k).carrier (D k).is_domain c j).mp h) h'

/-- Full restrictions to the given domains uniquely determine the global map. -/
theorem glueWith_unique (d : OriginalDomainStrongMatchingFamily A B D)
    (select : A.atlas.Index → ι) (hselect : ∀ i, ofChart i ≤ D (select i))
    (f : StrongHom A B)
    (hf : ∀ k, f.restrictSubspace (D k).carrier (D k).is_domain = d.localMap k) :
    f = d.glueWith select hselect := by
  apply StrongHom.ext_of_restrictSource
  intro i
  have h := congrArg (fun g => g.restrictOriginalDomain (hselect i)) (hf (select i))
  rw [StrongHom.restrictSubspace_restrictOriginalDomain] at h
  exact h.trans ((d.toStrongChartMapData select hselect).toStrongHom_restrictSource i).symm

/-- The complete glued strong map is independent of every containing-member
choice, not merely independent on spectrum points. -/
theorem glueWith_eq (d : OriginalDomainStrongMatchingFamily A B D)
    (select select' : A.atlas.Index → ι)
    (hselect : ∀ i, ofChart i ≤ D (select i))
    (hselect' : ∀ i, ofChart i ≤ D (select' i)) :
    d.glueWith select hselect = d.glueWith select' hselect' :=
  d.glueWith_unique select' hselect' _ (d.glueWith_restrictSubspace select hselect)

/-- Choose a containing member for every source chart and perform full descent. -/
def glue (d : OriginalDomainStrongMatchingFamily A B D) (hD : OriginalDomainCoversCharts D) :
    StrongHom A B :=
  d.glueWith (fun i => Classical.choose (hD i)) (fun i => Classical.choose_spec (hD i))

@[simp]
theorem glue_restrictSubspace (d : OriginalDomainStrongMatchingFamily A B D)
    (hD : OriginalDomainCoversCharts D) (k : ι) :
    (d.glue hD).restrictSubspace (D k).carrier (D k).is_domain = d.localMap k :=
  d.glueWith_restrictSubspace _ _ k

theorem glue_unique (d : OriginalDomainStrongMatchingFamily A B D)
    (hD : OriginalDomainCoversCharts D) (f : StrongHom A B)
    (hf : ∀ k, f.restrictSubspace (D k).carrier (D k).is_domain = d.localMap k) :
    f = d.glue hD :=
  d.glueWith_unique _ _ f hf

end OriginalDomainStrongMatchingFamily

namespace StrongHom

/-- The original ambient map gives a matching family by actual restriction. -/
def toOriginalDomainStrongMatchingFamily (f : StrongHom A B)
    (D : ι → A.atlas.OriginalChartDomain) : OriginalDomainStrongMatchingFamily A B D where
  localMap k := f.restrictSubspace (D k).carrier (D k).is_domain
  overlap k l := (f.restrictSubspace_restrictOriginalDomain
    (inf_le_left : D k ⊓ D l ≤ D k)).trans
      (f.restrictSubspace_restrictOriginalDomain
        (inf_le_right : D k ⊓ D l ≤ D l)).symm

@[simp]
theorem toOriginalDomainStrongMatchingFamily_glue (f : StrongHom A B)
    (D : ι → A.atlas.OriginalChartDomain) (hD : OriginalDomainCoversCharts D) :
    (f.toOriginalDomainStrongMatchingFamily D).glue hD = f :=
  ((f.toOriginalDomainStrongMatchingFamily D).glue_unique hD f (fun _ => rfl)).symm

end StrongHom

namespace OriginalDomainStrongMatchingFamily

variable {D : ι → A.atlas.OriginalChartDomain}

@[simp]
theorem glue_toOriginalDomainStrongMatchingFamily
    (d : OriginalDomainStrongMatchingFamily A B D) (hD : OriginalDomainCoversCharts D) :
    (d.glue hD).toOriginalDomainStrongMatchingFamily D = d := by
  apply ext
  funext k
  exact d.glue_restrictSubspace hD k

/-- Matching full local maps and global strong maps are equivalent whenever
the domain family contains every whole original source chart. -/
def strongHomEquiv (D : ι → A.atlas.OriginalChartDomain) (hD : OriginalDomainCoversCharts D) :
    OriginalDomainStrongMatchingFamily A B D ≃ StrongHom A B where
  toFun d := d.glue hD
  invFun f := f.toOriginalDomainStrongMatchingFamily D
  left_inv d := d.glue_toOriginalDomainStrongMatchingFamily hD
  right_inv f := f.toOriginalDomainStrongMatchingFamily_glue D hD

end OriginalDomainStrongMatchingFamily

end Langlands.Analytic.AffinoidAtlasPresentation
