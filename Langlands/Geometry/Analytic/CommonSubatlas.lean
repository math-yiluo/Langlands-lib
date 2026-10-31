import Langlands.Geometry.Analytic.AtlasSubatlas
import Langlands.Geometry.Analytic.AtlasTopology.RefinementComposition
import Mathlib.CategoryTheory.Category.Preorder

/-! # Common subatlases from downward-closed locally refining selections -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set CategoryTheory

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

/-- A selection contains every original chart whose domain is contained in
a selected original chart. No new affinoid domains are included by this condition. -/
def IsDownwardClosedSelection (a : IndexedAffinoidAtlas.{u, v, w} K X)
    (P : a.Index → Prop) : Prop :=
  ∀ i j, Set.range (a.chart i) ⊆ Set.range (a.chart j) → P j → P i

theorem selectedChartFamily_mono {P Q : a.Index → Prop} (hPQ : ∀ i, P i → Q i) :
    a.selectedChartFamily P ⊆ a.selectedChartFamily Q := by
  rintro U ⟨i, rfl⟩
  exact ⟨⟨i.val, hPQ i.val i.property⟩, rfl⟩

theorem IsLocallyRefiningSelection.mono {P Q : a.Index → Prop}
    (hP : a.IsLocallyRefiningSelection P) (hPQ : ∀ i, P i → Q i) :
    a.IsLocallyRefiningSelection Q :=
  AtlasTopology.LocallyRefines.mono hP (selectedChartFamily_mono hPQ) Subset.rfl

theorem isLocallyRefiningSelection_true (a : IndexedAffinoidAtlas.{u, v, w} K X) :
    a.IsLocallyRefiningSelection (fun _ => True) := by
  apply (AtlasTopology.LocallyRefines.refl _).mono ?_ Subset.rfl
  rintro U ⟨i, rfl⟩
  exact ⟨⟨i, trivial⟩, rfl⟩

theorem isDownwardClosedSelection_true (a : IndexedAffinoidAtlas.{u, v, w} K X) :
    a.IsDownwardClosedSelection (fun _ => True) := by
  intro _ _ _ _
  trivial

theorem IsDownwardClosedSelection.and {P Q : a.Index → Prop}
    (hP : a.IsDownwardClosedSelection P) (hQ : a.IsDownwardClosedSelection Q) :
    a.IsDownwardClosedSelection (fun i => P i ∧ Q i) := by
  intro i j h hij
  exact ⟨hP i j h hij.1, hQ i j h hij.2⟩

/-- Refine a selected P-chart through Q; downward closure keeps every
Q-witness in P, so the second-stage witnesses lie in the literal intersection. -/
theorem IsLocallyRefiningSelection.and {P Q : a.Index → Prop}
    (hP : a.IsLocallyRefiningSelection P) (hQ : a.IsLocallyRefiningSelection Q)
    (hdP : a.IsDownwardClosedSelection P) :
    a.IsLocallyRefiningSelection (fun i => P i ∧ Q i) := by
  apply hP.trans
  rintro U ⟨i, rfl⟩ x hx
  obtain ⟨σ, hf, hs, hm, hn⟩ := hQ _ ⟨i.val, rfl⟩ x hx
  refine ⟨σ, hf, ?_, hm, hn⟩
  intro V hV
  obtain ⟨j, hj⟩ := hs hV
  refine ⟨⟨j.val, ?_, j.property⟩, hj⟩
  apply hdP j.val i.val _ i.property
  change Set.range (a.chart j.val) = V at hj
  rw [hj]
  exact (hm V hV).1

/-- Downward-closed original-chart selections carrying finite relative local
refinement witnesses; no net or output atlas is assumed in this bundle. -/
structure RefiningSelection (a : IndexedAffinoidAtlas.{u, v, w} K X) where
  carrier : Set a.Index
  downward_closed : a.IsDownwardClosedSelection carrier
  locally_refining : a.IsLocallyRefiningSelection carrier

namespace RefiningSelection

instance : SetLike (RefiningSelection a) a.Index where
  coe := carrier
  coe_injective := by
    rintro ⟨P, hP, lP⟩ ⟨Q, hQ, lQ⟩ h
    cases h
    rfl

@[ext]
theorem ext {P Q : RefiningSelection a} (h : ∀ i, i ∈ P ↔ i ∈ Q) : P = Q :=
  SetLike.ext h

instance : SemilatticeInf (RefiningSelection a) where
  __ := PartialOrder.ofSetLike (RefiningSelection a) a.Index
  inf P Q := ⟨P.carrier ∩ Q.carrier,
    P.downward_closed.and Q.downward_closed,
    P.locally_refining.and Q.locally_refining P.downward_closed⟩
  inf_le_left _ _ _ h := h.1
  inf_le_right _ _ _ h := h.2
  le_inf _ _ _ hP hQ _ hi := ⟨hP hi, hQ hi⟩

instance : OrderTop (RefiningSelection a) where
  top := ⟨Set.univ, isDownwardClosedSelection_true a, isLocallyRefiningSelection_true a⟩
  le_top _ _ _ := trivial

@[simp]
theorem mem_inf (P Q : RefiningSelection a) (i : a.Index) :
    i ∈ P ⊓ Q ↔ i ∈ P ∧ i ∈ Q := Iff.rfl

@[simp]
theorem mem_top (i : a.Index) : i ∈ (⊤ : RefiningSelection a) := trivial

end RefiningSelection

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : AffinoidAtlasPresentation.{u, v, w} K)

/-- The actual same-space subatlas associated to a bundled refining selection. -/
def refiningSubpresentation (P : A.atlas.RefiningSelection) :
    AffinoidAtlasPresentation.{u, v, w} K :=
  A.subpresentation P.carrier P.locally_refining

/-- Inclusion of selections induces the published bounded identity chart maps. -/
def refiningSubatlasMap {P Q : A.atlas.RefiningSelection} (h : P ≤ Q) :
    A.refiningSubpresentation P ⟶ A.refiningSubpresentation Q :=
  A.subatlasMap P.carrier Q.carrier P.locally_refining Q.locally_refining (fun _ hi => h hi)

@[simp]
theorem refiningSubatlasMap_id (P : A.atlas.RefiningSelection) :
    A.refiningSubatlasMap (le_refl P) = 𝟙 (A.refiningSubpresentation P) :=
  A.subatlasMap_id P.carrier P.locally_refining _

theorem refiningSubatlasMap_comp {P Q R : A.atlas.RefiningSelection}
    (hPQ : P ≤ Q) (hQR : Q ≤ R) :
    A.refiningSubatlasMap hPQ ≫ A.refiningSubatlasMap hQR =
      A.refiningSubatlasMap (hPQ.trans hQR) :=
  A.subatlasMap_comp _ _ _ _ _ _ _ _ _

/-- Realize the order of refining selections by actual chosen atlas maps. -/
def refiningSubatlasFunctor : A.atlas.RefiningSelection ⥤
    AffinoidAtlasPresentation.{u, v, w} K where
  obj := A.refiningSubpresentation
  map h := A.refiningSubatlasMap (leOfHom h)
  map_id P := A.refiningSubatlasMap_id P
  map_comp f g := (A.refiningSubatlasMap_comp (leOfHom f) (leOfHom g)).symm

/-- The literal common selection supplies an actual atlas, with its net proved. -/
def commonSubpresentation (P Q : A.atlas.RefiningSelection) :
    AffinoidAtlasPresentation.{u, v, w} K :=
  A.refiningSubpresentation (P ⊓ Q)

/-- Canonical bounded chosen map to the first selected subatlas. -/
def commonSubatlasToLeft (P Q : A.atlas.RefiningSelection) :
    A.commonSubpresentation P Q ⟶ A.refiningSubpresentation P :=
  A.refiningSubatlasMap inf_le_left

/-- Canonical bounded chosen map to the second selected subatlas. -/
def commonSubatlasToRight (P Q : A.atlas.RefiningSelection) :
    A.commonSubpresentation P Q ⟶ A.refiningSubpresentation Q :=
  A.refiningSubatlasMap inf_le_right

/-- Both routes to the original atlas agree as full chosen arrows, including
all dependent bounded algebra pullbacks. -/
theorem commonSubatlas_diamond (P Q : A.atlas.RefiningSelection) :
    A.commonSubatlasToLeft P Q ≫ A.subatlasInclusion P.carrier P.locally_refining =
      A.commonSubatlasToRight P Q ≫ A.subatlasInclusion Q.carrier Q.locally_refining := by
  exact (A.subatlasMap_subatlasInclusion _ _ _ _ (fun _ hi => hi.1)).trans
    (A.subatlasMap_subatlasInclusion _ _ _ _ (fun _ hi => hi.2)).symm

@[simp]
theorem commonSubatlasToLeft_apply (P Q : A.atlas.RefiningSelection) (x : A.space) :
    (A.commonSubatlasToLeft P Q).baseMap x = x := rfl

@[simp]
theorem commonSubatlasToRight_apply (P Q : A.atlas.RefiningSelection) (x : A.space) :
    (A.commonSubatlasToRight P Q).baseMap x = x := rfl

@[simp]
theorem commonSubatlasToLeft_pullback (P Q : A.atlas.RefiningSelection)
    (i : (A.commonSubpresentation P Q).atlas.Index) :
    (A.commonSubatlasToLeft P Q).pullback i =
      BoundedAlgHom.id K (A.atlas.algebra i.val) := rfl

@[simp]
theorem commonSubatlasToRight_pullback (P Q : A.atlas.RefiningSelection)
    (i : (A.commonSubpresentation P Q).atlas.Index) :
    (A.commonSubatlasToRight P Q).pullback i =
      BoundedAlgHom.id K (A.atlas.algebra i.val) := rfl

end AffinoidAtlasPresentation

end Langlands.Analytic
