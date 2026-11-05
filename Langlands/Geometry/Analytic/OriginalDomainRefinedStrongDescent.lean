import Langlands.Geometry.Analytic.OriginalDomainStrongDescent
import Langlands.Geometry.Analytic.OriginalDomainSubatlasComparison
import Langlands.Geometry.Analytic.OriginalDomainCoverSelection

/-! # Full strong local maps glued after a constructed source refinement -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

open Set CategoryTheory IndexedAffinoidAtlas.OriginalChartDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

namespace StrongHom

/-- Select original source charts inside an actual domain, retaining every
admissible bounded pullback at the identical original chart. -/
def restrictSelectedDomainSource
    {S : A.atlas.OriginalChartDomain}
    (f : StrongHom (A.originalDomainPresentation S) B)
    (P : A.atlas.Index → Prop) (hP : A.atlas.IsLocallyRefiningSelection P) :
    StrongHom ((A.originalDomainSubatlasFunctor P hP).obj S) B where
  baseMap := f.baseMap
  target_exists c := f.target_exists ⟨c.val.val, c.property⟩
  pullback c j h := f.pullback ⟨c.val.val, c.property⟩ j h
  chart_comm c j h x := f.chart_comm ⟨c.val.val, c.property⟩ j h x
  restriction_comm c c' j j' hc hj h h' :=
    f.restriction_comm ⟨c.val.val, c.property⟩ ⟨c'.val.val, c'.property⟩ j j'
      (A.atlas.subspaceChart_subset S.carrier _ _
        ((A.atlas.subatlas P hP).chart_subset_of_subspaceSubset S.carrier c c' hc))
      hj h h'

@[simp]
theorem restrictSelectedDomainSource_apply
    {S : A.atlas.OriginalChartDomain}
    (f : StrongHom (A.originalDomainPresentation S) B)
    (P : A.atlas.Index → Prop) (hP : A.atlas.IsLocallyRefiningSelection P)
    (x : S) :
    (f.restrictSelectedDomainSource P hP).baseMap x = f.baseMap x := rfl

/-- Selecting source charts commutes with direct domain restriction, including
the entire bounded algebra homomorphism at every admissible pair. -/
theorem restrictSelectedDomainSource_restrictOriginalDomain
    {S T : A.atlas.OriginalChartDomain}
    (f : StrongHom (A.originalDomainPresentation T) B)
    (hST : S ≤ T) (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P) :
    StrongHom.restrictOriginalDomain (A := A.subpresentation P hP)
        (f.restrictSelectedDomainSource P hP)
        ((A.atlas.originalDomainSubatlasOrderIso P hP).monotone hST) =
      (f.restrictOriginalDomain hST).restrictSelectedDomainSource P hP := by
  refine ext_of_pullback rfl ?_
  intro c j h h'
  rfl

end StrongHom

namespace OriginalDomainStrongMatchingFamily

variable {ι : Type z} {D : ι → A.atlas.OriginalChartDomain}

/-- Transport the whole full strong matching family to selected original
source charts. Literal matching on all intersections is retained. -/
def selectedSource (d : OriginalDomainStrongMatchingFamily A B D)
    (P : A.atlas.Index → Prop) (hP : A.atlas.IsLocallyRefiningSelection P) :
    OriginalDomainStrongMatchingFamily (A.subpresentation P hP) B
      (fun k => A.atlas.originalDomainSubatlasOrderIso P hP (D k)) where
  localMap k := (d.localMap k).restrictSelectedDomainSource P hP
  overlap k l := by
    change StrongHom.restrictOriginalDomain (A := A.subpresentation P hP)
        ((d.localMap k).restrictSelectedDomainSource P hP)
        ((A.atlas.originalDomainSubatlasOrderIso P hP).monotone
          (inf_le_left : D k ⊓ D l ≤ D k)) =
      StrongHom.restrictOriginalDomain (A := A.subpresentation P hP)
        ((d.localMap l).restrictSelectedDomainSource P hP)
        ((A.atlas.originalDomainSubatlasOrderIso P hP).monotone
          (inf_le_right : D k ⊓ D l ≤ D l))
    rw [StrongHom.restrictSelectedDomainSource_restrictOriginalDomain,
      StrongHom.restrictSelectedDomainSource_restrictOriginalDomain, d.overlap]
    exact inf_le_left

end OriginalDomainStrongMatchingFamily

/-- The original charts contained in some cover member form a constructed
downward-closed refining selection. No saturation assumption is used. -/
def domainCoverSourceSelection {ι : Type z}
    (D : ι → A.atlas.OriginalChartDomain)
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {Set.univ}) : A.atlas.RefiningSelection :=
  IndexedAffinoidAtlas.coverRefiningSelection D (fun _ => ⊤) hD

/-- Every chart in the constructed source selection lies wholly inside a
transported cover member, as required by full strong chart reconstruction. -/
theorem domainCoverSourceSelection_coversCharts {ι : Type z}
    (D : ι → A.atlas.OriginalChartDomain)
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {Set.univ}) :
    OriginalDomainCoversCharts
      (A := A.subpresentation (domainCoverSourceSelection D hD).carrier
        (domainCoverSourceSelection D hD).locally_refining)
      (fun k => A.atlas.originalDomainSubatlasOrderIso
        (domainCoverSourceSelection D hD).carrier
        (domainCoverSourceSelection D hD).locally_refining (D k)) := by
  intro i
  obtain ⟨k, hi, _⟩ := i.property
  exact ⟨k, hi⟩

namespace OriginalDomainStrongMatchingFamily

variable {ι : Type z} {D : ι → A.atlas.OriginalChartDomain}

/-- Construct a full global strong numerator on a source refinement assembled
from the actual domain cover and the given literal full matching family. -/
def refinedGlue (d : OriginalDomainStrongMatchingFamily A B D)
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {Set.univ}) :
    StrongHom (A.subpresentation (domainCoverSourceSelection D hD).carrier
      (domainCoverSourceSelection D hD).locally_refining) B :=
  (d.selectedSource (domainCoverSourceSelection D hD).carrier
    (domainCoverSourceSelection D hD).locally_refining).glue
      (domainCoverSourceSelection_coversCharts D hD)

/-- On each selected-source domain the constructed strong numerator recovers
the complete original local map with its source charts selected. -/
theorem refinedGlue_restrictSubspace (d : OriginalDomainStrongMatchingFamily A B D)
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {Set.univ}) (k : ι) :
    (d.refinedGlue hD).restrictSubspace (D k).carrier
        (A.atlas.originalDomainSubatlasOrderIso
          (domainCoverSourceSelection D hD).carrier
          (domainCoverSourceSelection D hD).locally_refining (D k)).is_domain =
      (d.localMap k).restrictSelectedDomainSource
        (domainCoverSourceSelection D hD).carrier
        (domainCoverSourceSelection D hD).locally_refining :=
  (d.selectedSource (domainCoverSourceSelection D hD).carrier
    (domainCoverSourceSelection D hD).locally_refining).glue_restrictSubspace
      (domainCoverSourceSelection_coversCharts D hD) k

end OriginalDomainStrongMatchingFamily
end AffinoidAtlasPresentation

end Langlands.Analytic
