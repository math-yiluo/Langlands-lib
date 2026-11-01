import Langlands.Geometry.Analytic.OriginalChartDomains
import Langlands.Geometry.Analytic.StrongChartReconstruction

/-! # Full strong maps as a presheaf on actual original-chart domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation

open Set CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

namespace StrongHom

/-- Direct restriction retains exactly the larger domain's admissible pair
at the same original source chart. -/
theorem restrictOriginalDomain_admissible_iff
    {S T : A.atlas.OriginalChartDomain} (hST : S ≤ T)
    (f : StrongHom (A.originalDomainPresentation T) B)
    (c : A.atlas.SubspaceChart S.carrier) (j : B.atlas.Index) :
    (f.baseMap.comp (A.originalDomainMap hST).baseMap) ''
        Set.range ((A.originalDomainPresentation S).atlas.chart c) ⊆
          Set.range (B.atlas.chart j) ↔
      f.baseMap '' Set.range ((A.originalDomainPresentation T).atlas.chart
        ⟨c.val, c.property.trans hST⟩) ⊆ Set.range (B.atlas.chart j) := by
  constructor <;> intro h <;> rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  · exact h ⟨_, ⟨x, rfl⟩, rfl⟩
  · exact h ⟨_, ⟨x, rfl⟩, rfl⟩

/-- Restrict directly between two actual domains of the same original atlas.
The result uses the once-restricted source and every original bounded map. -/
def restrictOriginalDomain {S T : A.atlas.OriginalChartDomain}
    (f : StrongHom (A.originalDomainPresentation T) B) (hST : S ≤ T) :
    StrongHom (A.originalDomainPresentation S) B where
  baseMap := f.baseMap.comp (A.originalDomainMap hST).baseMap
  target_exists c := by
    obtain ⟨j, hj⟩ := f.target_exists ⟨c.val, c.property.trans hST⟩
    exact ⟨j, (restrictOriginalDomain_admissible_iff hST f c j).mpr hj⟩
  pullback c j h := f.pullback ⟨c.val, c.property.trans hST⟩ j
    ((restrictOriginalDomain_admissible_iff hST f c j).mp h)
  chart_comm c j h x := f.chart_comm ⟨c.val, c.property.trans hST⟩ j _ x
  restriction_comm c c' j j' hc hj h h' :=
    f.restriction_comm ⟨c.val, c.property.trans hST⟩
      ⟨c'.val, c'.property.trans hST⟩ j j'
      (A.atlas.subspaceChart_subset T.carrier _ _
        (A.atlas.chart_subset_of_subspaceSubset S.carrier c c' hc)) hj
      ((restrictOriginalDomain_admissible_iff hST f c j).mp h)
      ((restrictOriginalDomain_admissible_iff hST f c' j').mp h')

@[simp]
theorem restrictOriginalDomain_apply {S T : A.atlas.OriginalChartDomain}
    (f : StrongHom (A.originalDomainPresentation T) B) (hST : S ≤ T) (x : S) :
    (f.restrictOriginalDomain hST).baseMap x = f.baseMap (Set.inclusion hST x) := rfl

/-- Equality of the entire bounded map, with explicit admissibility transport. -/
theorem restrictOriginalDomain_pullback {S T : A.atlas.OriginalChartDomain}
    (f : StrongHom (A.originalDomainPresentation T) B) (hST : S ≤ T)
    (c : A.atlas.SubspaceChart S.carrier) (j : B.atlas.Index)
    (h : (f.restrictOriginalDomain hST).baseMap ''
      Set.range ((A.originalDomainPresentation S).atlas.chart c) ⊆
        Set.range (B.atlas.chart j)) :
    (f.restrictOriginalDomain hST).pullback c j h =
      f.pullback ⟨c.val, c.property.trans hST⟩ j
        ((restrictOriginalDomain_admissible_iff hST f c j).mp h) := rfl

@[simp]
theorem restrictOriginalDomain_refl {S : A.atlas.OriginalChartDomain}
    (f : StrongHom (A.originalDomainPresentation S) B) :
    f.restrictOriginalDomain (le_refl S) = f := by
  refine ext_of_pullback rfl ?_
  intro c j h h'
  rfl

/-- Two successive direct restrictions equal the direct restriction, including
all bounded pullbacks and not only the continuous base map. -/
theorem restrictOriginalDomain_trans {S T U : A.atlas.OriginalChartDomain}
    (f : StrongHom (A.originalDomainPresentation U) B) (hST : S ≤ T) (hTU : T ≤ U) :
    (f.restrictOriginalDomain hTU).restrictOriginalDomain hST =
      f.restrictOriginalDomain (hST.trans hTU) := by
  refine ext_of_pullback rfl ?_
  intro c j h h'
  rfl

/-- Direct restriction agrees with the published subspace restriction of an
ambient strong map, with the same once-restricted source presentation. -/
@[simp]
theorem restrictSubspace_restrictOriginalDomain (f : StrongHom A B)
    {S T : A.atlas.OriginalChartDomain} (hST : S ≤ T) :
    (f.restrictSubspace T.carrier T.is_domain).restrictOriginalDomain hST =
      f.restrictSubspace S.carrier S.is_domain := by
  refine ext_of_pullback rfl ?_
  intro c j h h'
  rfl

end StrongHom

/-- Full strong maps into a fixed arbitrary target, with direct restriction
on the fixed-original-chart domain inclusion category. -/
def originalDomainStrongPresheaf (A B : AffinoidAtlasPresentation.{u, v, w} K) :
    A.atlas.OriginalChartDomainᵒᵖ ⥤ Type (max u v w) where
  obj S := StrongHom (A.originalDomainPresentation S.unop) B
  map h := TypeCat.ofHom (fun f => f.restrictOriginalDomain (leOfHom h.unop))
  map_id S := by
    apply ConcreteCategory.hom_ext
    intro f
    exact f.restrictOriginalDomain_refl
  map_comp h k := by
    apply ConcreteCategory.hom_ext
    intro f
    exact (f.restrictOriginalDomain_trans (leOfHom k.unop) (leOfHom h.unop)).symm

end Langlands.Analytic.AffinoidAtlasPresentation
