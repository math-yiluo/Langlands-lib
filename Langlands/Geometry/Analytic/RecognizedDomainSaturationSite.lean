import Langlands.Geometry.Analytic.RecognizedDomainFiniteRefinement
import Langlands.Geometry.Analytic.RecognizedDomainSite

/-! # Domain-site invariance under saturation after full recognition -/

noncomputable section

universe u v w t s r

namespace Langlands.Analytic.IndexedAffinoidAtlas

open Set CategoryTheory PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- A finite actual chart cover of a Hausdorff subset supplies the contained
original-chart quasinet, without any overlap or output-atlas input. -/
theorem isOriginalChartDomain_of_finite_chart_cover (S : Set X) [T2Space S]
    {ι : Type r} [Finite ι] (c : ι → a.Index)
    (hcover : (⋃ i, Set.range (a.chart (c i))) = S) :
    a.IsOriginalChartDomain S := by
  have hsub (i : ι) : Set.range (a.chart (c i)) ⊆ S := by
    rw [← hcover]
    exact Set.subset_iUnion (fun j => Set.range (a.chart (c j))) i
  let f (i : ι) : Set S := Subtype.val ⁻¹' Set.range (a.chart (c i))
  apply AtlasTopology.isQuasinet_of_finite_closedCover
    (Set.range f) (Set.finite_range f)
  · rintro T ⟨i, rfl⟩
    exact ⟨Set.range (a.chart (c i)), Set.mem_range_self _, hsub i, rfl⟩
  · rintro T ⟨i, rfl⟩
    have hc : IsCompact (f i) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage'
        (isCompact_range (a.isEmbedding_chart (c i)).continuous)
        (by simpa only [Subtype.range_coe] using hsub i)
    exact hc.isClosed
  · apply Set.eq_univ_of_forall
    intro x
    have hx : x.val ∈ ⋃ i, Set.range (a.chart (c i)) := hcover.symm ▸ x.property
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨f i, ⟨i, rfl⟩, hi⟩

namespace RecognizedSubset

variable {a} (V : a.RecognizedSubset)

/-- The actual spectrum of a full domain identifies its literal ambient
subset with the induced topology. -/
def domainLocusHomeomorph (D : Domain K V.algebra) :
    BanachSpectrum D.algebra ≃ₜ V.domainLocus D :=
  (V.isEmbedding_domainAmbientMap D).toHomeomorph.trans
    (Homeomorph.setCongr (V.range_domainAmbientMap D))

@[simp]
theorem domainLocusHomeomorph_apply_coe (D : Domain K V.algebra)
    (x : BanachSpectrum D.algebra) :
    (V.domainLocusHomeomorph D x : X) = V.domainAmbientMap D x := rfl

end RecognizedSubset

/-- The actual original local-domain piece supplies a chart of the
already constructed saturated atlas, at exactly its literal ambient subset. -/
def fullRecognitionDomainPieceIndex (V : a.saturatedAtlas.RecognizedSubset)
    (D : Domain K V.algebra) (i : Fin V.property.cover.size) : a.saturatedAtlas.Index :=
  ⟨(a.fullRecognitionDomainPiece V D i).locus,
    ⟨a.fullRecognitionDomainPiece V D i, rfl⟩⟩

theorem range_fullRecognitionDomainPieceIndex (V : a.saturatedAtlas.RecognizedSubset)
    (D : Domain K V.algebra) (i : Fin V.property.cover.size) :
    Set.range (a.saturatedAtlas.chart (a.fullRecognitionDomainPieceIndex V D i)) =
      (a.fullRecognitionDomainPiece V D i).locus :=
  a.range_saturatedChart _

/-- Every full domain in a full-recognition chart has the original
contained-chart domain condition for the saturated input atlas. -/
theorem fullRecognitionDomainLocus_isOriginalChartDomain
    (V : a.saturatedAtlas.RecognizedSubset) (D : Domain K V.algebra) :
    a.saturatedAtlas.IsOriginalChartDomain (V.domainLocus D) := by
  let : T2Space (V.domainLocus D) := (V.domainLocusHomeomorph D).t2Space
  apply a.saturatedAtlas.isOriginalChartDomain_of_finite_chart_cover
    (V.domainLocus D) (a.fullRecognitionDomainPieceIndex V D)
  simp_rw [a.range_fullRecognitionDomainPieceIndex V D]
  exact a.fullRecognitionDomainPiece_covers V D

theorem fullRecognitionLocalDomain_isOriginalChartDomain
    (U : LocalDomain a.fullRecognitionAtlas) :
    a.saturatedAtlas.IsOriginalChartDomain U.locus :=
  a.fullRecognitionDomainLocus_isOriginalChartDomain U.index U.domain

/-- Each chart added by saturation after full recognition has a finite
relative refinement by charts from the saturated input atlas. -/
theorem chartFamily_locallyRefines_saturatedFullRecognitionAtlas :
    AtlasTopology.LocallyRefines
      (Set.range (fun i => Set.range (a.saturatedAtlas.chart i)))
      (Set.range (fun i => Set.range (a.fullRecognitionAtlas.saturatedAtlas.chart i))) := by
  rintro S ⟨U, rfl⟩
  have hU : a.saturatedAtlas.IsOriginalChartDomain
      (Set.range (a.fullRecognitionAtlas.saturatedAtlas.chart U)) := by
    change a.saturatedAtlas.IsOriginalChartDomain
      (Set.range (a.fullRecognitionAtlas.saturatedChart U))
    rw [a.fullRecognitionAtlas.range_saturatedChart U,
      ← a.fullRecognitionAtlas.saturatedRepresentative_locus U]
    exact a.fullRecognitionLocalDomain_isOriginalChartDomain
      (a.fullRecognitionAtlas.saturatedRepresentative U)
  exact (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp hU
    _ (Set.mem_singleton _)

/-- The twice enlarged chart family contains every original saturated
chart range, using the already constructed original recognition copies. -/
theorem chartFamily_subset_saturatedFullRecognitionAtlas :
    Set.range (fun i => Set.range (a.saturatedAtlas.chart i)) ⊆
      Set.range (fun i => Set.range (a.fullRecognitionAtlas.saturatedAtlas.chart i)) := by
  rw [a.fullRecognitionAtlas.saturatedAtlas_chartFamily]
  exact a.saturatedAtlas.chartFamily_subset_recognitionAtlas.trans
    a.fullRecognitionAtlas.chartFamily_subset_localDomainFamily

theorem saturatedFullRecognitionAtlas_locallyRefines_chartFamily :
    AtlasTopology.LocallyRefines
      (Set.range (fun i => Set.range (a.fullRecognitionAtlas.saturatedAtlas.chart i)))
      (Set.range (fun i => Set.range (a.saturatedAtlas.chart i))) :=
  (AtlasTopology.LocallyRefines.refl
    (Set.range (fun i => Set.range (a.saturatedAtlas.chart i)))).mono
      a.chartFamily_subset_saturatedFullRecognitionAtlas Subset.rfl

/-- Further actual local domains after full recognition do not change
the domain subsets of the saturated input atlas. -/
theorem isOriginalChartDomain_saturatedFullRecognitionAtlas_iff (S : Set X) :
    a.fullRecognitionAtlas.saturatedAtlas.IsOriginalChartDomain S ↔
      a.saturatedAtlas.IsOriginalChartDomain S := by
  constructor
  · intro hS
    exact hS.of_locallyRefines a.chartFamily_locallyRefines_saturatedFullRecognitionAtlas
  · intro hS
    exact hS.of_locallyRefines a.saturatedFullRecognitionAtlas_locallyRefines_chartFamily

/-- In particular, saturation preserves the domain condition after the
constructed full recognition step. -/
theorem isOriginalChartDomain_fullRecognitionAtlas_saturation_iff (S : Set X) :
    a.fullRecognitionAtlas.saturatedAtlas.IsOriginalChartDomain S ↔
      a.fullRecognitionAtlas.IsOriginalChartDomain S :=
  (a.isOriginalChartDomain_saturatedFullRecognitionAtlas_iff S).trans
    (a.isOriginalChartDomain_fullRecognitionAtlas_iff S).symm

/-- The comparison retains each actual subset and its inclusion order. -/
def saturatedFullRecognitionDomainOrderIso :
    OriginalChartDomain a.saturatedAtlas ≃o
      OriginalChartDomain a.fullRecognitionAtlas.saturatedAtlas :=
  OriginalChartDomain.refinementOrderIso
    a.chartFamily_locallyRefines_saturatedFullRecognitionAtlas
    a.saturatedFullRecognitionAtlas_locallyRefines_chartFamily

@[simp]
theorem coe_saturatedFullRecognitionDomainOrderIso
    (S : OriginalChartDomain a.saturatedAtlas) :
    (a.saturatedFullRecognitionDomainOrderIso S : Set X) = S := rfl

@[simp]
theorem coe_saturatedFullRecognitionDomainOrderIso_symm
    (S : OriginalChartDomain a.fullRecognitionAtlas.saturatedAtlas) :
    (a.saturatedFullRecognitionDomainOrderIso.symm S : Set X) = S := rfl

def saturatedFullRecognitionDomainEquivalence :
    OriginalChartDomain a.saturatedAtlas ≌
      OriginalChartDomain a.fullRecognitionAtlas.saturatedAtlas :=
  OriginalChartDomain.refinementEquivalence
    a.chartFamily_locallyRefines_saturatedFullRecognitionAtlas
    a.saturatedFullRecognitionAtlas_locallyRefines_chartFamily

theorem sieveFamily_functorPullback_saturatedFullRecognition
    (S : OriginalChartDomain a.saturatedAtlas)
    (R : Sieve (a.saturatedFullRecognitionDomainEquivalence.functor.obj S)) :
    OriginalChartDomain.sieveFamily
        (R.functorPullback a.saturatedFullRecognitionDomainEquivalence.functor) =
      OriginalChartDomain.sieveFamily R :=
  OriginalChartDomain.sieveFamily_functorPullback_refinement
    a.chartFamily_locallyRefines_saturatedFullRecognitionAtlas
    a.saturatedFullRecognitionAtlas_locallyRefines_chartFamily S R

/-- Preservation and reflection hold for every covering sieve. -/
theorem functorPullback_mem_saturatedFullRecognitionDomainTopology_iff
    (S : OriginalChartDomain a.saturatedAtlas)
    (R : Sieve (a.saturatedFullRecognitionDomainEquivalence.functor.obj S)) :
    R.functorPullback a.saturatedFullRecognitionDomainEquivalence.functor ∈
        OriginalChartDomain.quasinetTopology a.saturatedAtlas S ↔
      R ∈ OriginalChartDomain.quasinetTopology a.fullRecognitionAtlas.saturatedAtlas
        (a.saturatedFullRecognitionDomainEquivalence.functor.obj S) :=
  OriginalChartDomain.functorPullback_mem_quasinetTopology_iff
    a.chartFamily_locallyRefines_saturatedFullRecognitionAtlas
    a.saturatedFullRecognitionAtlas_locallyRefines_chartFamily S R

theorem ofArrows_saturatedFullRecognition_mem_iff {ι : Type*}
    (S : OriginalChartDomain a.saturatedAtlas)
    (D : ι → OriginalChartDomain a.saturatedAtlas) (f : ∀ i, D i ⟶ S) :
    Sieve.ofArrows D f ∈ OriginalChartDomain.quasinetTopology a.saturatedAtlas S ↔
      Sieve.ofArrows
        (fun i => a.saturatedFullRecognitionDomainEquivalence.functor.obj (D i))
        (fun i => a.saturatedFullRecognitionDomainEquivalence.functor.map (f i)) ∈
          OriginalChartDomain.quasinetTopology a.fullRecognitionAtlas.saturatedAtlas
            (a.saturatedFullRecognitionDomainEquivalence.functor.obj S) :=
  OriginalChartDomain.ofArrows_refinement_mem_iff
    a.saturatedFullRecognitionAtlas_locallyRefines_chartFamily S D f

/-- Sheaves with arbitrary categorical coefficients correspond by
restriction along the inverse literal-subset site equivalence. -/
def saturatedFullRecognitionDomainSheafEquivalence (C : Type t) [Category.{s} C] :
    Sheaf (OriginalChartDomain.quasinetTopology a.saturatedAtlas) C ≌
      Sheaf (OriginalChartDomain.quasinetTopology a.fullRecognitionAtlas.saturatedAtlas) C :=
  OriginalChartDomain.refinementSheafEquivalence
    a.chartFamily_locallyRefines_saturatedFullRecognitionAtlas
    a.saturatedFullRecognitionAtlas_locallyRefines_chartFamily C

@[simp]
theorem saturatedFullRecognitionDomainSheafEquivalence_obj_obj
    {C : Type t} [Category.{s} C]
    (F : Sheaf (OriginalChartDomain.quasinetTopology a.saturatedAtlas) C)
    (S : OriginalChartDomain a.fullRecognitionAtlas.saturatedAtlas) :
    ((a.saturatedFullRecognitionDomainSheafEquivalence C).functor.obj F).obj.obj
        (Opposite.op S) =
      F.obj.obj (Opposite.op (a.saturatedFullRecognitionDomainOrderIso.symm S)) := rfl

@[simp]
theorem saturatedFullRecognitionDomainSheafEquivalence_map_app
    {C : Type t} [Category.{s} C]
    {F G : Sheaf (OriginalChartDomain.quasinetTopology a.saturatedAtlas) C} (α : F ⟶ G)
    (S : OriginalChartDomain a.fullRecognitionAtlas.saturatedAtlas) :
    ((a.saturatedFullRecognitionDomainSheafEquivalence C).functor.map α).hom.app
        (Opposite.op S) =
      α.hom.app (Opposite.op (a.saturatedFullRecognitionDomainOrderIso.symm S)) := rfl

end Langlands.Analytic.IndexedAffinoidAtlas
