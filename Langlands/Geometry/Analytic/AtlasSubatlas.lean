import Langlands.Geometry.Analytic.AtlasTopology.Refinement
import Langlands.Geometry.Analytic.ChosenAtlasMorphisms

/-! # Same-space subatlases selected by relative local refinement -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology CategoryTheory
open scoped Topology

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Exactly the domains of the selected original charts, on the same space. -/
def selectedChartFamily (P : a.Index → Prop) : Set (Set X) :=
  Set.range (fun i : {i : a.Index // P i} => Set.range (a.chart i.val))

theorem selectedChartFamily_subset (P : a.Index → Prop) :
    a.selectedChartFamily P ⊆ Set.range (fun i => Set.range (a.chart i)) := by
  rintro U ⟨i, rfl⟩
  exact ⟨i.val, rfl⟩

/-- The selected original charts give finite relative neighborhood
refinements inside every original chart. This does not assume an output net. -/
def IsLocallyRefiningSelection (P : a.Index → Prop) : Prop :=
  AtlasTopology.LocallyRefines (a.selectedChartFamily P)
    (Set.range (fun i => Set.range (a.chart i)))

theorem isNet_selectedChartFamily (P : a.Index → Prop)
    (hP : a.IsLocallyRefiningSelection P) :
    AtlasTopology.IsNet (a.selectedChartFamily P) :=
  a.isNet_chartFamily.of_locallyRefines (a.selectedChartFamily_subset P) hP

/-- Select original charts without changing the underlying space or any
chart algebra, embedding, bounded restriction, or domain factorization. -/
def subatlas (P : a.Index → Prop) (hP : a.IsLocallyRefiningSelection P) :
    IndexedAffinoidAtlas.{u, v, w} K X where
  Index := {i : a.Index // P i}
  algebra i := a.algebra i.val
  chart i := a.chart i.val
  isEmbedding_chart i := a.isEmbedding_chart i.val
  chartDomain_injective := by
    intro i j hij
    exact Subtype.ext (a.chartDomain_injective hij)
  locallyHausdorff := a.locallyHausdorff
  isNet_chartFamily := a.isNet_selectedChartFamily P hP
  restriction i j h := a.restriction i.val j.val h
  restriction_chart i j h := a.restriction_chart i.val j.val h
  restriction_universal i j h := a.restriction_universal i.val j.val h
  restriction_id i h := a.restriction_id i.val h
  restriction_comp i j k hij hjk hik := a.restriction_comp i.val j.val k.val hij hjk hik

@[simp]
theorem subatlas_algebra (P : a.Index → Prop) (hP : a.IsLocallyRefiningSelection P)
    (i : {i : a.Index // P i}) :
    (a.subatlas P hP).algebra i = a.algebra i.val := rfl

@[simp]
theorem subatlas_chart (P : a.Index → Prop) (hP : a.IsLocallyRefiningSelection P)
    (i : {i : a.Index // P i}) :
    (a.subatlas P hP).chart i = a.chart i.val := rfl

@[simp]
theorem subatlas_restriction (P : a.Index → Prop) (hP : a.IsLocallyRefiningSelection P)
    (i j : {i : a.Index // P i})
    (h : Set.range ((a.subatlas P hP).chart i) ⊆
      Set.range ((a.subatlas P hP).chart j)) :
    (a.subatlas P hP).restriction i j h = a.restriction i.val j.val h := rfl

theorem subatlas_chartFamily (P : a.Index → Prop) (hP : a.IsLocallyRefiningSelection P) :
    Set.range (fun i => Set.range ((a.subatlas P hP).chart i)) =
      a.selectedChartFamily P := rfl

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : AffinoidAtlasPresentation.{u, v, w} K)

/-- The selected atlas on exactly the original topological space. -/
def subpresentation (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P) :
    AffinoidAtlasPresentation.{u, v, w} K where
  space := A.space
  atlas := A.atlas.subatlas P hP

/-- The canonical same-space chosen arrow retains chart indices and uses
the actual bounded identity on each selected algebra. -/
def subatlasInclusion (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P) : A.subpresentation P hP ⟶ A where
  baseMap := ContinuousMap.id A.space
  indexMap i := i.val
  index_mono _ _ h := h
  pullback i := BoundedAlgHom.id K (A.atlas.algebra i.val)
  chart_comm _ _ := rfl
  restriction_comm _ _ _ := rfl

/-- Inclusions between two locally refining selections on the same space. -/
def subatlasMap (P Q : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P)
    (hQ : A.atlas.IsLocallyRefiningSelection Q) (hPQ : ∀ i, P i → Q i) :
    A.subpresentation P hP ⟶ A.subpresentation Q hQ where
  baseMap := ContinuousMap.id A.space
  indexMap i := ⟨i.val, hPQ i.val i.property⟩
  index_mono _ _ h := h
  pullback i := BoundedAlgHom.id K (A.atlas.algebra i.val)
  chart_comm _ _ := rfl
  restriction_comm _ _ _ := rfl

@[simp]
theorem subatlasMap_id (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P) (hPP : ∀ i, P i → P i) :
    A.subatlasMap P P hP hP hPP = 𝟙 (A.subpresentation P hP) :=
  Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

theorem subatlasMap_comp (P Q R : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P)
    (hQ : A.atlas.IsLocallyRefiningSelection Q)
    (hR : A.atlas.IsLocallyRefiningSelection R)
    (hPQ : ∀ i, P i → Q i) (hQR : ∀ i, Q i → R i) (hPR : ∀ i, P i → R i) :
    A.subatlasMap P Q hP hQ hPQ ≫ A.subatlasMap Q R hQ hR hQR =
      A.subatlasMap P R hP hR hPR :=
  Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

@[simp]
theorem subatlasMap_subatlasInclusion (P Q : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P)
    (hQ : A.atlas.IsLocallyRefiningSelection Q) (hPQ : ∀ i, P i → Q i) :
    A.subatlasMap P Q hP hQ hPQ ≫ A.subatlasInclusion Q hQ =
      A.subatlasInclusion P hP :=
  Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

@[simp]
theorem subatlasInclusion_apply (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P) (x : A.space) :
    (A.subatlasInclusion P hP).baseMap x = x := rfl

@[simp]
theorem subatlasInclusion_pullback (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P) (i : {i : A.atlas.Index // P i}) :
    (A.subatlasInclusion P hP).pullback i =
      BoundedAlgHom.id K (A.atlas.algebra i.val) := rfl

@[simp]
theorem spaceFunctor_subatlasInclusion (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P) :
    (spaceFunctor (K := K)).map (A.subatlasInclusion P hP) = 𝟙 A.space := rfl

end AffinoidAtlasPresentation

end Langlands.Analytic
