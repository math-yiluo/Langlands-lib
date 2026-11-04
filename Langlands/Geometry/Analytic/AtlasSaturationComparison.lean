import Langlands.Geometry.Analytic.SaturatedAffinoidAtlas
import Langlands.Geometry.Analytic.AtlasReindexing

/-! # Full strong comparisons with the constructed enlarged affinoid atlas -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

def originalLocalDomain (i : a.Index) : LocalDomain a :=
  ⟨i, Domain.whole K (a.algebra i)⟩

theorem originalLocalDomain_locus (i : a.Index) :
    (a.originalLocalDomain i).locus = Set.range (a.chart i) := Set.image_univ

theorem originalLocalDomain_ambientMap (i : a.Index) (x : BanachSpectrum (a.algebra i)) :
    (a.originalLocalDomain i).ambientMap x = a.chart i x :=
  congrArg (a.chart i) (BanachSpectrum.ext fun _ => rfl)

/-- On original whole charts, actual local-domain arrows retain precisely
the original atlas bounded restriction. -/
theorem originalLocalDomain_restriction (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j))
    (f : a.originalLocalDomain i ⟶ a.originalLocalDomain j) :
    f.restriction = a.restriction i j h := by
  have hU : (a.originalLocalDomain i).locus ⊆ Set.range (a.chart j) := by
    rw [a.originalLocalDomain_locus i]
    exact h
  have hV : (a.originalLocalDomain j).locus ⊆ Set.range (a.chart j) := by
    rw [a.originalLocalDomain_locus j]
  have hf := f.comp_chart j hU hV
  have h₁ := congrArg (fun q : BoundedAlgHom K (a.algebra j) (a.algebra j) =>
    f.restriction.comp q) (a.domainChartRestriction_self j (Domain.whole K (a.algebra j)) hV)
  have h₂ := a.domainChartRestriction_of_chartSubset i j (Domain.whole K (a.algebra i)) hU h
  exact h₁.symm.trans (hf.trans h₂)

def originalToSaturatedInclusion (i : a.Index) (S : a.localDomainFamily)
    (h : Set.range (a.chart i) ⊆ Set.range (a.saturatedChart S)) :
    a.originalLocalDomain i ⟶ a.saturatedRepresentative S :=
  LocalDomain.Inclusion.ofSubset _ _ (by
    rw [a.originalLocalDomain_locus, ← (a.saturatedRepresentative S).range_ambientMap]
    exact h)

def saturatedToOriginalInclusion (S : a.localDomainFamily) (i : a.Index)
    (h : Set.range (a.saturatedChart S) ⊆ Set.range (a.chart i)) :
    a.saturatedRepresentative S ⟶ a.originalLocalDomain i :=
  LocalDomain.Inclusion.ofSubset _ _ (by
    rw [a.originalLocalDomain_locus, ← (a.saturatedRepresentative S).range_ambientMap]
    exact h)

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

variable (A : AffinoidAtlasPresentation.{u, v, w} K)

/-- The actual enlarged atlas on the literal original ambient space. -/
def saturatedPresentation : AffinoidAtlasPresentation.{u, v, v} K where
  space := A.space
  atlas := A.atlas.saturatedAtlas

/-- Reindex both sides into one universe, retaining the original charts and maps. -/
def saturationSource : AffinoidAtlasPresentation.{u, v, max v w} K :=
  A.reindex (Equiv.ulift : ULift.{v} A.atlas.Index ≃ A.atlas.Index)

def saturationTarget : AffinoidAtlasPresentation.{u, v, max v w} K :=
  A.saturatedPresentation.reindex
    (Equiv.ulift : ULift.{w} A.atlas.localDomainFamily ≃ A.atlas.localDomainFamily)

/-- Full all-admissible-pair strong map from the original atlas to its
constructed enlargement, with identity ambient map. -/
def toSaturation : StrongHom A.saturationSource A.saturationTarget where
  baseMap := ContinuousMap.id A.space
  target_exists i := by
    refine ⟨ULift.up (A.atlas.originalSaturatedIndex i.down), ?_⟩
    change id '' Set.range (A.atlas.chart i.down) ⊆
      Set.range (A.atlas.saturatedChart (A.atlas.originalSaturatedIndex i.down))
    rw [Set.image_id, A.atlas.range_saturatedChart]
    exact Subset.rfl
  pullback i S h := (A.atlas.originalToSaturatedInclusion i.down S.down
    (fun x hx => h ⟨x, hx, rfl⟩)).restriction
  chart_comm i S h x :=
    ((A.atlas.originalToSaturatedInclusion i.down S.down _).ambientMap_naturality x).trans
      (A.atlas.originalLocalDomain_ambientMap i.down x)
  restriction_comm i i' S T hi hST h h' := by
    let p := A.atlas.originalToSaturatedInclusion i.down S.down
      (fun x hx => h ⟨x, hx, rfl⟩)
    let q := A.atlas.originalToSaturatedInclusion i'.down T.down
      (fun x hx => h' ⟨x, hx, rfl⟩)
    let f : A.atlas.originalLocalDomain i.down ⟶ A.atlas.originalLocalDomain i'.down :=
      IndexedAffinoidAtlas.LocalDomain.Inclusion.ofSubset _ _ (by
        rw [A.atlas.originalLocalDomain_locus, A.atlas.originalLocalDomain_locus]
        exact hi)
    let g := A.atlas.saturatedInclusion S.down T.down hST
    have heq := congrArg IndexedAffinoidAtlas.LocalDomain.Inclusion.restriction
      (@Subsingleton.elim (IndexedAffinoidAtlas.LocalDomain.Inclusion
        (A.atlas.originalLocalDomain i.down) (A.atlas.saturatedRepresentative T.down))
        inferInstance (f ≫ q) (p ≫ g))
    rw [IndexedAffinoidAtlas.LocalDomain.Inclusion.restriction_comp,
      A.atlas.originalLocalDomain_restriction i.down i'.down hi f] at heq
    exact heq

/-- Full all-admissible-pair strong map from the enlarged atlas to the
original one, with the same identity ambient map. -/
def fromSaturation : StrongHom A.saturationTarget A.saturationSource where
  baseMap := ContinuousMap.id A.space
  target_exists S := by
    refine ⟨ULift.up (A.atlas.saturatedRepresentative S.down).index, ?_⟩
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨(A.atlas.saturatedRepresentative S.down).domain.spectrumMap x, rfl⟩
  pullback S i h := (A.atlas.saturatedToOriginalInclusion S.down i.down
    (fun x hx => h ⟨x, hx, rfl⟩)).restriction
  chart_comm S i h x :=
    (A.atlas.originalLocalDomain_ambientMap i.down
      (BanachSpectrum.comap
        (A.atlas.saturatedToOriginalInclusion S.down i.down _).restriction.toBoundedRingHom x)).symm.trans
      ((A.atlas.saturatedToOriginalInclusion S.down i.down _).ambientMap_naturality x)
  restriction_comm S T i j hST hij h h' := by
    let p := A.atlas.saturatedToOriginalInclusion S.down i.down
      (fun x hx => h ⟨x, hx, rfl⟩)
    let q := A.atlas.saturatedToOriginalInclusion T.down j.down
      (fun x hx => h' ⟨x, hx, rfl⟩)
    let f := A.atlas.saturatedInclusion S.down T.down hST
    let g : A.atlas.originalLocalDomain i.down ⟶ A.atlas.originalLocalDomain j.down :=
      IndexedAffinoidAtlas.LocalDomain.Inclusion.ofSubset _ _ (by
        rw [A.atlas.originalLocalDomain_locus, A.atlas.originalLocalDomain_locus]
        exact hij)
    have heq := congrArg IndexedAffinoidAtlas.LocalDomain.Inclusion.restriction
      (@Subsingleton.elim (IndexedAffinoidAtlas.LocalDomain.Inclusion
        (A.atlas.saturatedRepresentative S.down) (A.atlas.originalLocalDomain j.down))
        inferInstance (f ≫ q) (p ≫ g))
    rw [IndexedAffinoidAtlas.LocalDomain.Inclusion.restriction_comp,
      IndexedAffinoidAtlas.LocalDomain.Inclusion.restriction_comp,
      A.atlas.originalLocalDomain_restriction i.down j.down hij g] at heq
    exact heq

theorem isQuasiIso_toSaturation : A.toSaturation.IsQuasiIso := by
  refine ⟨IsHomeomorph.id, ?_⟩
  intro i S h
  have hlocus : A.toSaturation.chartImageLocus i S =
      (A.atlas.saturatedRepresentative S.down).ambientMap ⁻¹'
        (A.atlas.originalLocalDomain i.down).locus := by
    change (A.atlas.saturatedChart S.down) ⁻¹' (id '' Set.range (A.atlas.chart i.down)) = _
    rw [Set.image_id, A.atlas.originalLocalDomain_locus]
    rfl
  rw [hlocus]
  exact (A.atlas.originalToSaturatedInclusion i.down S.down
    (fun x hx => h ⟨x, hx, rfl⟩)).represents

theorem isQuasiIso_fromSaturation : A.fromSaturation.IsQuasiIso := by
  refine ⟨IsHomeomorph.id, ?_⟩
  intro S i h
  have hlocus : A.fromSaturation.chartImageLocus S i =
      (A.atlas.originalLocalDomain i.down).ambientMap ⁻¹'
        (A.atlas.saturatedRepresentative S.down).locus := by
    ext x
    change A.atlas.chart i.down x ∈
        id '' Set.range (A.atlas.saturatedRepresentative S.down).ambientMap ↔
      (A.atlas.originalLocalDomain i.down).ambientMap x ∈
        (A.atlas.saturatedRepresentative S.down).locus
    erw [Set.image_id, (A.atlas.saturatedRepresentative S.down).range_ambientMap,
      A.atlas.originalLocalDomain_ambientMap]
  rw [hlocus]
  exact (A.atlas.saturatedToOriginalInclusion S.down i.down
    (fun x hx => h ⟨x, hx, rfl⟩)).represents

end AffinoidAtlasPresentation
end Langlands.Analytic
