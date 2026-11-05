import Langlands.Geometry.Analytic.QuotientDomainStrongRefinement

/-! # Unique gluing of arbitrary quotient-domain matching families -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.SaturatedAtlasPresentation.SourceCategory

open CategoryTheory Set AffinoidAtlasPresentation
open IndexedAffinoidAtlas.OriginalChartDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K} {ι : Type z}
  {D : ι → A.presentation.atlas.OriginalChartDomain}

namespace QuotientDomainMatchingFamily

/-- Glue arbitrary quotient matching arrows by the full strong refinement
constructed from their actual local chart representatives. -/
def glue (d : QuotientDomainMatchingFamily A B D)
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {Set.univ}) :
    ofPresentation A ⟶ ofPresentation B :=
  glueStrongDomainFamily d.strongRefinement (d.strongRefinement_cover hD)

/-- The constructed global arrow recovers every full map on the refined
ambient original-chart domains. -/
theorem glue_refinement (d : QuotientDomainMatchingFamily A B D)
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {Set.univ})
    (t : d.RefinementIndex) :
    domainInclusion A (d.refinementDomain t) ≫ d.glue hD =
      strongFunctor.map (d.refinementMap t) :=
  glueStrongDomainFamily_restrict d.strongRefinement (d.strongRefinement_cover hD) t

/-- The global quotient glue recovers every original arbitrary local arrow,
using full quotient separation on its selected original-chart cover. -/
theorem glue_restrict (d : QuotientDomainMatchingFamily A B D)
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {Set.univ}) (k : ι) :
    domainInclusion A (D k) ≫ d.glue hD = d.localMap k := by
  apply eq_of_domainCover (A := A.originalDomain (D k))
    (fun i : {i : (A.originalDomain (D k)).presentation.atlas.Index //
      i ∈ (d.chartData k).selection} => ofChart i.val) (d.chartData_cover k)
  intro i
  have : IsIso (domainNestedMap (A := A) (D k) (ofChart i.val)) := by
    change IsIso (domainNestedIso (A := A) (D k) (ofChart i.val)).hom
    infer_instance
  apply (cancel_epi (domainNestedMap (A := A) (D k) (ofChart i.val))).1
  erw [← Category.assoc, domainNestedMap_inclusion, ← Category.assoc,
    domainMap_inclusion, ← Category.assoc, domainNestedMap_inclusion]
  exact (d.glue_refinement hD ⟨k, i⟩).trans
    (d.refinementMap_represents ⟨k, i⟩).symm

/-- Any quotient arrow with the given arbitrary domain restrictions is the
constructed glue. No global strong representative is required. -/
theorem glue_unique (d : QuotientDomainMatchingFamily A B D)
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {Set.univ})
    (F : ofPresentation A ⟶ ofPresentation B)
    (hF : ∀ k, domainInclusion A (D k) ≫ F = d.localMap k) :
    F = d.glue hD :=
  eq_of_domainCover D hD F (d.glue hD)
    (fun k => (hF k).trans (d.glue_restrict hD k).symm)

/-- Every arbitrary matching family on an original-domain quasinet cover
has a unique glue in the actual source quotient. -/
theorem existsUnique_glue (d : QuotientDomainMatchingFamily A B D)
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {Set.univ}) :
    ∃! F : ofPresentation A ⟶ ofPresentation B,
      ∀ k, domainInclusion A (D k) ≫ F = d.localMap k :=
  ⟨d.glue hD, d.glue_restrict hD, fun F hF => d.glue_unique hD F hF⟩

end QuotientDomainMatchingFamily
end Langlands.Analytic.SaturatedAtlasPresentation.SourceCategory
