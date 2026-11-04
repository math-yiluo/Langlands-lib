import Langlands.Geometry.Analytic.AtlasDomainNet

/-! # The constructed affinoid atlas on all local full domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Original chart domains remain literal indices of the enlarged net. -/
def originalSaturatedIndex (i : a.Index) : a.localDomainFamily :=
  ⟨Set.range (a.chart i), a.chartFamily_subset_localDomainFamily (Set.mem_range_self i)⟩

/-- Choose an actual full-domain presentation for each new member, keeping
whole original-chart presentations whenever that member is an original chart. -/
def saturatedRepresentative (S : a.localDomainFamily) : LocalDomain a := by
  classical
  exact if h : ∃ i, Set.range (a.chart i) = S.val then
      ⟨h.choose, Domain.whole K (a.algebra h.choose)⟩
    else
      Classical.choose S.property

theorem saturatedRepresentative_locus (S : a.localDomainFamily) :
    (a.saturatedRepresentative S).locus = S.val := by
  unfold saturatedRepresentative
  split_ifs with h
  · exact Set.image_univ.trans h.choose_spec
  · exact Classical.choose_spec S.property

/-- Original chart-domain injectivity makes the chosen original presentation
exactly the given whole-chart presentation. -/
theorem saturatedRepresentative_original (i : a.Index) :
    a.saturatedRepresentative (a.originalSaturatedIndex i) =
      (⟨i, Domain.whole K (a.algebra i)⟩ : LocalDomain a) := by
  unfold saturatedRepresentative
  split_ifs with h
  · have hi : h.choose = i := a.chartDomain_injective h.choose_spec
    exact congrArg (fun t : a.Index =>
      (⟨t, Domain.whole K (a.algebra t)⟩ : LocalDomain a)) hi
  · exact (h ⟨i, rfl⟩).elim

def saturatedChart (S : a.localDomainFamily) :
    BanachSpectrum (a.saturatedRepresentative S).algebra → X :=
  (a.saturatedRepresentative S).ambientMap

theorem range_saturatedChart (S : a.localDomainFamily) :
    Set.range (a.saturatedChart S) = S.val :=
  (a.saturatedRepresentative S).range_ambientMap.trans (a.saturatedRepresentative_locus S)

theorem saturatedChartFamily :
    Set.range (fun S : a.localDomainFamily => Set.range (a.saturatedChart S)) =
      a.localDomainFamily := by
  ext U
  constructor
  · rintro ⟨S, rfl⟩
    change Set.range (a.saturatedChart S) ∈ a.localDomainFamily
    rw [a.range_saturatedChart S]
    exact S.property
  · intro hU
    exact ⟨⟨U, hU⟩, a.range_saturatedChart ⟨U, hU⟩⟩

/-- The actual local-domain arrow between chosen presentations of nested members. -/
def saturatedInclusion (S T : a.localDomainFamily)
    (h : Set.range (a.saturatedChart S) ⊆ Set.range (a.saturatedChart T)) :
    a.saturatedRepresentative S ⟶ a.saturatedRepresentative T :=
  LocalDomain.Inclusion.ofSubset _ _ (by
    rw [← (a.saturatedRepresentative S).range_ambientMap,
      ← (a.saturatedRepresentative T).range_ambientMap]
    exact h)

/-- Construct the entire atlas on the enlarged local-affinoid net. Its
algebras and every bounded restriction are actual constructed objects. -/
def saturatedAtlas : IndexedAffinoidAtlas.{u, v, v} K X where
  Index := a.localDomainFamily
  algebra S := (a.saturatedRepresentative S).algebra
  chart := a.saturatedChart
  isEmbedding_chart S := (a.saturatedRepresentative S).isEmbedding_ambientMap
  chartDomain_injective S T h := Subtype.ext
    ((a.range_saturatedChart S).symm.trans (h.trans (a.range_saturatedChart T)))
  locallyHausdorff := a.locallyHausdorff
  isNet_chartFamily := by
    rw [a.saturatedChartFamily]
    exact a.isNet_localDomainFamily
  restriction S T h := (a.saturatedInclusion S T h).restriction
  restriction_chart S T h x := (a.saturatedInclusion S T h).ambientMap_naturality x
  restriction_universal S T h R φ hφ := by
    apply (a.saturatedInclusion S T h).represents.2.2 R φ
    intro x
    rw [← (a.saturatedRepresentative S).range_ambientMap]
    exact hφ x
  restriction_id S h := congrArg LocalDomain.Inclusion.restriction
    (@Subsingleton.elim (LocalDomain.Inclusion (a.saturatedRepresentative S)
      (a.saturatedRepresentative S)) inferInstance
      (a.saturatedInclusion S S h) (𝟙 (a.saturatedRepresentative S)))
  restriction_comp S T U hST hTU hSU := congrArg LocalDomain.Inclusion.restriction
    (@Subsingleton.elim (LocalDomain.Inclusion (a.saturatedRepresentative S)
      (a.saturatedRepresentative U)) inferInstance
      (a.saturatedInclusion S U hSU)
      (a.saturatedInclusion S T hST ≫ a.saturatedInclusion T U hTU))

@[simp]
theorem saturatedAtlas_algebra (S : a.localDomainFamily) :
    a.saturatedAtlas.algebra S = (a.saturatedRepresentative S).algebra := rfl

@[simp]
theorem saturatedAtlas_chart (S : a.localDomainFamily) :
    a.saturatedAtlas.chart S = a.saturatedChart S := rfl

theorem saturatedAtlas_chartFamily :
    Set.range (fun S : a.saturatedAtlas.Index => Set.range (a.saturatedAtlas.chart S)) =
      a.localDomainFamily :=
  a.saturatedChartFamily

theorem saturatedAtlas_original_range (i : a.Index) :
    Set.range (a.saturatedAtlas.chart (a.originalSaturatedIndex i)) =
      Set.range (a.chart i) :=
  a.range_saturatedChart (a.originalSaturatedIndex i)

theorem saturatedAtlas_original_algebra (i : a.Index) :
    a.saturatedAtlas.algebra (a.originalSaturatedIndex i) = a.algebra i := by
  change (a.saturatedRepresentative (a.originalSaturatedIndex i)).algebra = _
  rw [a.saturatedRepresentative_original i]
  rfl

/-- Every local-domain presentation has a canonical actual bounded comparison
with the presentation chosen by the enlarged atlas for its ambient subset. -/
def localDomainSaturatedEquiv (U : LocalDomain a) :
    BoundedAlgEquiv K U.algebra
      (a.saturatedRepresentative ⟨U.locus, ⟨U, rfl⟩⟩).algebra :=
  LocalDomain.boundedEquivOfLocusEq U _
    (a.saturatedRepresentative_locus ⟨U.locus, ⟨U, rfl⟩⟩).symm

end Langlands.Analytic.IndexedAffinoidAtlas
