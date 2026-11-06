import Langlands.Geometry.Analytic.RecognizedAffinoidAtlas
import Langlands.Geometry.Analytic.OriginalDomainRefinement

/-! # The domain site is unchanged by the constructed recognition atlas -/

noncomputable section

universe u v w t s

namespace Langlands.Analytic.IndexedAffinoidAtlas

open Set CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Every recognized literal subset is already a domain for the original
chart family, by its finite Hausdorff original-chart cover. -/
theorem RecognizedSubset.isOriginalChartDomain (U : a.RecognizedSubset) :
    a.IsOriginalChartDomain U.locus :=
  U.val.isQuasinet_restrictedChartFamily

theorem chartFamily_subset_recognitionAtlas :
    Set.range (fun i => Set.range (a.chart i)) ⊆
      Set.range (fun i => Set.range (a.recognitionAtlas.chart i)) := by
  rintro S ⟨i, rfl⟩
  exact ⟨a.originalRecognitionIndex i, a.recognitionAtlas_original_range i⟩

/-- Original charts give finite relative neighborhood refinements inside
every recognized chart, retaining the actual chart subset. -/
theorem chartFamily_locallyRefines_recognitionAtlas :
    AtlasTopology.LocallyRefines
      (Set.range (fun i => Set.range (a.chart i)))
      (Set.range (fun i => Set.range (a.recognitionAtlas.chart i))) := by
  rintro S ⟨U, rfl⟩
  have hU : a.IsOriginalChartDomain
      (Set.range (a.recognitionAtlas.chart U)) := by
    change a.IsOriginalChartDomain (Set.range U.chart)
    rw [U.range_chart]
    exact U.isOriginalChartDomain a
  exact (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp hU
    _ (Set.mem_singleton _)

/-- The recognition atlas also refines the original family, since it
contains every original chart range. -/
theorem recognitionAtlas_locallyRefines_chartFamily :
    AtlasTopology.LocallyRefines
      (Set.range (fun i => Set.range (a.recognitionAtlas.chart i)))
      (Set.range (fun i => Set.range (a.chart i))) :=
  (AtlasTopology.LocallyRefines.refl
    (Set.range (fun i => Set.range (a.chart i)))).mono
      a.chartFamily_subset_recognitionAtlas Subset.rfl

/-- Recognition preserves and reflects the actual original-chart-domain
condition on every subset of the unchanged ambient space. -/
theorem isOriginalChartDomain_recognitionAtlas_iff (S : Set X) :
    a.recognitionAtlas.IsOriginalChartDomain S ↔ a.IsOriginalChartDomain S := by
  constructor
  · intro hS
    exact hS.of_locallyRefines a.chartFamily_locallyRefines_recognitionAtlas
  · intro hS
    exact hS.of_locallyRefines a.recognitionAtlas_locallyRefines_chartFamily

/-- The constructed comparison retains literal subsets and their order. -/
def recognitionDomainOrderIso :
    OriginalChartDomain a ≃o OriginalChartDomain a.recognitionAtlas :=
  OriginalChartDomain.refinementOrderIso
    a.chartFamily_locallyRefines_recognitionAtlas
    a.recognitionAtlas_locallyRefines_chartFamily

@[simp]
theorem coe_recognitionDomainOrderIso (S : OriginalChartDomain a) :
    (a.recognitionDomainOrderIso S : Set X) = S := rfl

@[simp]
theorem coe_recognitionDomainOrderIso_symm
    (S : OriginalChartDomain a.recognitionAtlas) :
    (a.recognitionDomainOrderIso.symm S : Set X) = S := rfl

/-- An equivalence of the actual inclusion categories, rather than a
comparison of only the covered points. -/
def recognitionDomainEquivalence :
    OriginalChartDomain a ≌ OriginalChartDomain a.recognitionAtlas :=
  OriginalChartDomain.refinementEquivalence
    a.chartFamily_locallyRefines_recognitionAtlas
    a.recognitionAtlas_locallyRefines_chartFamily

/-- Every sieve retains exactly the same family of actual source subsets. -/
theorem sieveFamily_functorPullback_recognition
    (S : OriginalChartDomain a)
    (R : Sieve (a.recognitionDomainEquivalence.functor.obj S)) :
    OriginalChartDomain.sieveFamily
        (R.functorPullback a.recognitionDomainEquivalence.functor) =
      OriginalChartDomain.sieveFamily R :=
  OriginalChartDomain.sieveFamily_functorPullback_refinement
    a.chartFamily_locallyRefines_recognitionAtlas
    a.recognitionAtlas_locallyRefines_chartFamily S R

/-- The actual quasinet Grothendieck topology is preserved and reflected
on all sieves. -/
theorem functorPullback_mem_recognitionDomainTopology_iff
    (S : OriginalChartDomain a)
    (R : Sieve (a.recognitionDomainEquivalence.functor.obj S)) :
    R.functorPullback a.recognitionDomainEquivalence.functor ∈
        OriginalChartDomain.quasinetTopology a S ↔
      R ∈ OriginalChartDomain.quasinetTopology a.recognitionAtlas
        (a.recognitionDomainEquivalence.functor.obj S) :=
  OriginalChartDomain.functorPullback_mem_quasinetTopology_iff
    a.chartFamily_locallyRefines_recognitionAtlas
    a.recognitionAtlas_locallyRefines_chartFamily S R

/-- Arbitrary generated covering families agree under the same-subset
comparison, including empty families and empty domains. -/
theorem ofArrows_recognition_mem_iff {ι : Type*}
    (S : OriginalChartDomain a) (D : ι → OriginalChartDomain a)
    (f : ∀ i, D i ⟶ S) :
    Sieve.ofArrows D f ∈ OriginalChartDomain.quasinetTopology a S ↔
      Sieve.ofArrows
        (fun i => a.recognitionDomainEquivalence.functor.obj (D i))
        (fun i => a.recognitionDomainEquivalence.functor.map (f i)) ∈
          OriginalChartDomain.quasinetTopology a.recognitionAtlas
            (a.recognitionDomainEquivalence.functor.obj S) :=
  OriginalChartDomain.ofArrows_refinement_mem_iff
    a.recognitionAtlas_locallyRefines_chartFamily S D f

/-- Sheaves with values in any coefficient category correspond by
restriction along the inverse literal-subset comparison. -/
def recognitionDomainSheafEquivalence (C : Type t) [Category.{s} C] :
    Sheaf (OriginalChartDomain.quasinetTopology a) C ≌
      Sheaf (OriginalChartDomain.quasinetTopology a.recognitionAtlas) C :=
  OriginalChartDomain.refinementSheafEquivalence
    a.chartFamily_locallyRefines_recognitionAtlas
    a.recognitionAtlas_locallyRefines_chartFamily C

@[simp]
theorem recognitionDomainSheafEquivalence_obj_obj
    {C : Type t} [Category.{s} C]
    (F : Sheaf (OriginalChartDomain.quasinetTopology a) C)
    (S : OriginalChartDomain a.recognitionAtlas) :
    ((a.recognitionDomainSheafEquivalence C).functor.obj F).obj.obj
        (Opposite.op S) =
      F.obj.obj (Opposite.op (a.recognitionDomainOrderIso.symm S)) := rfl

@[simp]
theorem recognitionDomainSheafEquivalence_map_app
    {C : Type t} [Category.{s} C]
    {F G : Sheaf (OriginalChartDomain.quasinetTopology a) C} (α : F ⟶ G)
    (S : OriginalChartDomain a.recognitionAtlas) :
    ((a.recognitionDomainSheafEquivalence C).functor.map α).hom.app
        (Opposite.op S) =
      α.hom.app (Opposite.op (a.recognitionDomainOrderIso.symm S)) := rfl

/-- Applied to the enlarged full local-domain atlas, recognition retains
its actual domain subsets. -/
theorem isOriginalChartDomain_fullRecognitionAtlas_iff (S : Set X) :
    a.fullRecognitionAtlas.IsOriginalChartDomain S ↔
      a.saturatedAtlas.IsOriginalChartDomain S :=
  a.saturatedAtlas.isOriginalChartDomain_recognitionAtlas_iff S

def fullRecognitionDomainOrderIso :
    OriginalChartDomain a.saturatedAtlas ≃o
      OriginalChartDomain a.fullRecognitionAtlas :=
  a.saturatedAtlas.recognitionDomainOrderIso

/-- The full local-domain version compares the actual enlarged domain
site with its constructed full recognition extension. -/
def fullRecognitionDomainSheafEquivalence (C : Type t) [Category.{s} C] :
    Sheaf (OriginalChartDomain.quasinetTopology a.saturatedAtlas) C ≌
      Sheaf (OriginalChartDomain.quasinetTopology a.fullRecognitionAtlas) C :=
  a.saturatedAtlas.recognitionDomainSheafEquivalence C

end Langlands.Analytic.IndexedAffinoidAtlas
