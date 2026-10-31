import Langlands.Geometry.Analytic.AtlasRestriction
import Langlands.Geometry.Analytic.StrongAtlasMaps

/-! # Actual subspaces covered locally by contained original charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology CategoryTheory
open scoped Topology

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Every point has a finite relative neighborhood made of original chart
domains contained in the subspace and containing that point. -/
def IsOriginalChartDomain (S : Set X) : Prop :=
  AtlasTopology.IsQuasinet
    (AtlasTopology.restrictedFamily (Set.range (fun i => Set.range (a.chart i))) S)

theorem isOriginalChartDomain_chart (i : a.Index) :
    a.IsOriginalChartDomain (Set.range (a.chart i)) :=
  (a.isNet_chartFamily.restrict_member ⟨i, rfl⟩).1

theorem isOriginalChartDomain_empty : a.IsOriginalChartDomain ∅ := by
  intro x
  exact False.elim x.property

/-- Exactly the original charts contained in the indicated subspace. -/
def SubspaceChart (S : Set X) :=
  {i : a.Index // Set.range (a.chart i) ⊆ S}

/-- The original spectrum embedding with its codomain restricted. -/
def subspaceChart (S : Set X) (c : a.SubspaceChart S) :
    BanachSpectrum (a.algebra c.val) → S :=
  fun x => ⟨a.chart c.val x, c.property ⟨x, rfl⟩⟩

theorem range_subspaceChart (S : Set X) (c : a.SubspaceChart S) :
    Set.range (a.subspaceChart S c) =
      (Subtype.val ⁻¹' Set.range (a.chart c.val) : Set S) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

theorem chart_subset_of_subspaceSubset (S : Set X) (c d : a.SubspaceChart S)
    (h : Set.range (a.subspaceChart S c) ⊆ Set.range (a.subspaceChart S d)) :
    Set.range (a.chart c.val) ⊆ Set.range (a.chart d.val) := by
  rw [a.range_subspaceChart, a.range_subspaceChart] at h
  intro x hx
  exact h (show (⟨x, c.property hx⟩ : S) ∈
    (Subtype.val ⁻¹' Set.range (a.chart c.val) : Set S) from hx)

theorem subspaceChart_subset (S : Set X) (c d : a.SubspaceChart S)
    (h : Set.range (a.chart c.val) ⊆ Set.range (a.chart d.val)) :
    Set.range (a.subspaceChart S c) ⊆ Set.range (a.subspaceChart S d) := by
  rw [a.range_subspaceChart, a.range_subspaceChart]
  exact Set.preimage_mono h

theorem subspaceChartFamily_eq (S : Set X) :
    Set.range (fun c => Set.range (a.subspaceChart S c)) =
      AtlasTopology.restrictedFamily (Set.range (fun i => Set.range (a.chart i))) S := by
  ext U
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Set.range (a.chart c.val), ⟨c.val, rfl⟩, c.property,
      a.range_subspaceChart S c⟩
  · rintro ⟨_, ⟨i, rfl⟩, hiS, rfl⟩
    exact ⟨⟨i, hiS⟩, a.range_subspaceChart S ⟨i, hiS⟩⟩

/-- The ambient net supplies every intersection axiom; the input supplies
only finite relative neighborhoods in the subspace. -/
theorem isNet_subspaceChartFamily (S : Set X) (hS : a.IsOriginalChartDomain S) :
    AtlasTopology.IsNet (Set.range (fun c => Set.range (a.subspaceChart S c))) := by
  rw [a.subspaceChartFamily_eq]
  exact a.isNet_chartFamily.restrict S hS

include a in
/-- Local Hausdorffness passes to the actual induced subspace topology. -/
theorem locallyHausdorff_subspace (S : Set X) (x : S) :
    ∃ U : Set S, U ∈ 𝓝 x ∧ T2Space U := by
  obtain ⟨U, hU, hT2⟩ := a.locallyHausdorff x.val
  let : T2Space U := hT2
  refine ⟨Subtype.val ⁻¹' U, continuous_subtype_val.continuousAt hU, ?_⟩
  exact ((IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).codRestrict U
    (fun y : (Subtype.val ⁻¹' U : Set S) => y.property)).t2Space

/-- Construct the actual atlas on any subspace covered locally by contained
original charts. All algebras and bounded restrictions remain original. -/
def subspaceAtlas (S : Set X) (hS : a.IsOriginalChartDomain S) :
    IndexedAffinoidAtlas.{u, v, w} K S where
  Index := a.SubspaceChart S
  algebra c := a.algebra c.val
  chart := a.subspaceChart S
  isEmbedding_chart c := (a.isEmbedding_chart c.val).codRestrict S _
  chartDomain_injective := by
    intro c d h
    apply Subtype.ext
    apply a.chartDomain_injective
    exact Set.Subset.antisymm
      (a.chart_subset_of_subspaceSubset S c d h.subset)
      (a.chart_subset_of_subspaceSubset S d c h.symm.subset)
  locallyHausdorff := a.locallyHausdorff_subspace S
  isNet_chartFamily := a.isNet_subspaceChartFamily S hS
  restriction c d h := a.restriction c.val d.val
    (a.chart_subset_of_subspaceSubset S c d h)
  restriction_chart c d h x := Subtype.ext (a.restriction_chart c.val d.val _ x)
  restriction_universal c d h R φ hφ := by
    apply a.restriction_universal c.val d.val _ R φ
    intro x
    obtain ⟨y, hy⟩ := hφ x
    exact ⟨y, congrArg Subtype.val hy⟩
  restriction_id c h := a.restriction_id c.val _
  restriction_comp c d e hcd hde hce := a.restriction_comp c.val d.val e.val _ _ _

@[simp]
theorem subspaceAtlas_algebra (S : Set X) (hS : a.IsOriginalChartDomain S)
    (c : a.SubspaceChart S) :
    (a.subspaceAtlas S hS).algebra c = a.algebra c.val := rfl

@[simp]
theorem subspaceAtlas_chart_val (S : Set X) (hS : a.IsOriginalChartDomain S)
    (c : a.SubspaceChart S) (x : BanachSpectrum (a.algebra c.val)) :
    ((a.subspaceAtlas S hS).chart c x).val = a.chart c.val x := rfl

@[simp]
theorem subspaceAtlas_restriction (S : Set X) (hS : a.IsOriginalChartDomain S)
    (c d : a.SubspaceChart S)
    (h : Set.range ((a.subspaceAtlas S hS).chart c) ⊆
      Set.range ((a.subspaceAtlas S hS).chart d)) :
    (a.subspaceAtlas S hS).restriction c d h =
      a.restriction c.val d.val (a.chart_subset_of_subspaceSubset S c d h) := rfl

/-- The earlier actual original-chart atlas is this subspace construction. -/
theorem subspaceAtlas_chart (i : a.Index) :
    a.subspaceAtlas (Set.range (a.chart i)) (a.isOriginalChartDomain_chart i) =
      a.chartAtlas i := rfl

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : AffinoidAtlasPresentation.{u, v, w} K)

/-- The original-chart atlas on the actual subspace. -/
def subspacePresentation (S : Set A.space) (hS : A.atlas.IsOriginalChartDomain S) :
    AffinoidAtlasPresentation.{u, v, w} K where
  space := TopCat.of S
  atlas := A.atlas.subspaceAtlas S hS

/-- Actual inclusion with original chart indices and bounded identities. -/
def subspaceInclusion (S : Set A.space) (hS : A.atlas.IsOriginalChartDomain S) :
    A.subspacePresentation S hS ⟶ A where
  baseMap := ⟨Subtype.val, continuous_subtype_val⟩
  indexMap c := c.val
  index_mono := A.atlas.chart_subset_of_subspaceSubset S
  pullback c := BoundedAlgHom.id K (A.atlas.algebra c.val)
  chart_comm _ _ := rfl
  restriction_comm _ _ _ := rfl

/-- Actual inclusion between nested original-chart subspaces. -/
def subspaceMap (S T : Set A.space)
    (hS : A.atlas.IsOriginalChartDomain S) (hT : A.atlas.IsOriginalChartDomain T)
    (hST : S ⊆ T) :
    A.subspacePresentation S hS ⟶ A.subspacePresentation T hT where
  baseMap := ⟨Set.inclusion hST, continuous_subtype_val.subtype_mk _⟩
  indexMap c := ⟨c.val, c.property.trans hST⟩
  index_mono c d h := A.atlas.subspaceChart_subset T _ _
    (A.atlas.chart_subset_of_subspaceSubset S c d h)
  pullback c := BoundedAlgHom.id K (A.atlas.algebra c.val)
  chart_comm _ _ := rfl
  restriction_comm _ _ _ := rfl

@[simp]
theorem subspaceMap_id (S : Set A.space) (hS : A.atlas.IsOriginalChartDomain S)
    (hSS : S ⊆ S) :
    A.subspaceMap S S hS hS hSS = 𝟙 (A.subspacePresentation S hS) :=
  Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

theorem subspaceMap_comp (S T U : Set A.space)
    (hS : A.atlas.IsOriginalChartDomain S) (hT : A.atlas.IsOriginalChartDomain T)
    (hU : A.atlas.IsOriginalChartDomain U) (hST : S ⊆ T) (hTU : T ⊆ U) (hSU : S ⊆ U) :
    A.subspaceMap S T hS hT hST ≫ A.subspaceMap T U hT hU hTU =
      A.subspaceMap S U hS hU hSU :=
  Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

@[simp]
theorem subspaceMap_subspaceInclusion (S T : Set A.space)
    (hS : A.atlas.IsOriginalChartDomain S) (hT : A.atlas.IsOriginalChartDomain T)
    (hST : S ⊆ T) :
    A.subspaceMap S T hS hT hST ≫ A.subspaceInclusion T hT =
      A.subspaceInclusion S hS :=
  Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

variable {A} {B : AffinoidAtlasPresentation.{u, v, w} K}

namespace StrongHom

theorem restrictSubspace_admissible_iff (f : StrongHom A B)
    (S : Set A.space) (hS : A.atlas.IsOriginalChartDomain S)
    (c : A.atlas.SubspaceChart S) (j : B.atlas.Index) :
    (f.baseMap.comp (A.subspaceInclusion S hS).baseMap) ''
        Set.range ((A.subspacePresentation S hS).atlas.chart c) ⊆
          Set.range (B.atlas.chart j) ↔
      f.baseMap '' Set.range (A.atlas.chart c.val) ⊆
        Set.range (B.atlas.chart j) := by
  constructor <;> intro h <;> rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  · exact h ⟨_, ⟨x, rfl⟩, rfl⟩
  · exact h ⟨_, ⟨x, rfl⟩, rfl⟩

/-- Restrict a full strong map to any actual original-chart subspace,
retaining the complete target and every original admissible pullback. -/
def restrictSubspace (f : StrongHom A B)
    (S : Set A.space) (hS : A.atlas.IsOriginalChartDomain S) :
    StrongHom (A.subspacePresentation S hS) B where
  baseMap := f.baseMap.comp (A.subspaceInclusion S hS).baseMap
  target_exists c := by
    obtain ⟨j, hj⟩ := f.target_exists c.val
    exact ⟨j, (f.restrictSubspace_admissible_iff S hS c j).mpr hj⟩
  pullback c j h := f.pullback c.val j
    ((f.restrictSubspace_admissible_iff S hS c j).mp h)
  chart_comm c j h x := f.chart_comm c.val j _ x
  restriction_comm c c' j j' hc hj h h' :=
    f.restriction_comm c.val c'.val j j'
      (A.atlas.chart_subset_of_subspaceSubset S c c' hc) hj
      ((f.restrictSubspace_admissible_iff S hS c j).mp h)
      ((f.restrictSubspace_admissible_iff S hS c' j').mp h')

@[simp]
theorem restrictSubspace_apply (f : StrongHom A B)
    (S : Set A.space) (hS : A.atlas.IsOriginalChartDomain S) (x : S) :
    (f.restrictSubspace S hS).baseMap x = f.baseMap x.val := rfl

@[simp]
theorem restrictSubspace_pullback (f : StrongHom A B)
    (S : Set A.space) (hS : A.atlas.IsOriginalChartDomain S)
    (c : A.atlas.SubspaceChart S) (j : B.atlas.Index)
    (h : (f.restrictSubspace S hS).baseMap ''
      Set.range ((A.subspacePresentation S hS).atlas.chart c) ⊆
        Set.range (B.atlas.chart j)) :
    (f.restrictSubspace S hS).pullback c j h =
      f.pullback c.val j ((f.restrictSubspace_admissible_iff S hS c j).mp h) := rfl

end StrongHom

/-- The full inclusion retains every admissible original bounded restriction.
There is no directedness hypothesis. -/
def subspaceStrongInclusion (A : AffinoidAtlasPresentation.{u, v, w} K)
    (S : Set A.space) (hS : A.atlas.IsOriginalChartDomain S) :
    StrongHom (A.subspacePresentation S hS) A :=
  (StrongHom.id A).restrictSubspace S hS

@[simp]
theorem subspaceStrongInclusion_apply (S : Set A.space)
    (hS : A.atlas.IsOriginalChartDomain S) (x : S) :
    (A.subspaceStrongInclusion S hS).baseMap x = x.val := rfl

end AffinoidAtlasPresentation

end Langlands.Analytic
