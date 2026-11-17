import Langlands.Geometry.Analytic.FibreProductConeAlignment
import Langlands.Geometry.Analytic.FibreProductChartConeLift
import Langlands.Geometry.Analytic.CompatibleOriginalDomainDescent

/-! # Actual source-refined complete fibre-product cone lifts -/

noncomputable section

universe u v

namespace Langlands.Analytic.FibreProduct

open Set CategoryTheory AffinoidAtlasPresentation IndexedAffinoidAtlas.OriginalChartDomain
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C T : AffinoidAtlasPresentation.{u, v, v} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)
  (a : CompatibleStrongHom T A) (b : CompatibleStrongHom T B)

/-- Nonempty original source charts admitting actual good pair alignment.
Empty source spaces require no domain indices. -/
def ConeDomainIndex : Type v :=
  {i : T.atlas.Index // alignedSourceCharts f g a b i ∧ (range (T.atlas.chart i)).Nonempty}

/-- The actual original chart domains on which complete local lifts are built. -/
def coneDomain (i : ConeDomainIndex f g a b) : T.atlas.OriginalChartDomain := ofChart i.val

/-- Removing empty aligned charts preserves the full finite neighborhood cover. -/
theorem coneDomain_locallyRefines
    (hT : T.atlas.HasAllLocalDomains) (hA : A.atlas.HasAllLocalDomains)
    (hB : B.atlas.HasAllLocalDomains) (hab : a.comp f = b.comp g) :
    AtlasTopology.LocallyRefines (range (fun i => (coneDomain f g a b i).carrier)) {univ} := by
  rintro _ rfl x _
  obtain ⟨σ, hf, hs, hm, hn⟩ :=
    (T.atlas.isNet_selectedChartFamily _ (alignedSourceCharts_locallyRefining f g a b hT hA hB hab)).1 x
  refine ⟨σ, hf, ?_, fun V hV => ⟨subset_univ _, hm V hV⟩, ?_⟩
  · intro V hV
    obtain ⟨i, hi⟩ := hs hV
    refine ⟨⟨i.val, i.property, ?_⟩, hi⟩
    change range (T.atlas.chart i.val) = V at hi
    rw [hi]
    exact ⟨x, hm V hV⟩
  · simpa only [nhdsWithin_univ] using hn

variable [Small.{v} (chartSystem f g).Space]
  (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
  (hC : C.atlas.HasAllLocalDomains) (hT : T.atlas.HasAllLocalDomains)
  (hab : a.comp f = b.comp g)

/-- Choose the actual aligned pair and construct the entire local map using
its bounded algebra pushout, including both complete projection identities. -/
def coneDomainLift (i : ConeDomainIndex f g a b) :
    CompatibleStrongHom (T.originalDomainPresentation (coneDomain f g a b i))
      (smallPresentation f g hA hB hC) :=
  let p := Classical.choose i.property.1
  let hp := Classical.choose_spec i.property.1
  coneChartLift f g a b hab hA hB hC hT i.val p hp.1 hp.2.1 hp.2.2 (by
    obtain ⟨_, s, _⟩ := i.property.2
    exact ⟨s⟩)

theorem coneDomainLift_comp_fst (i : ConeDomainIndex f g a b) :
    (coneDomainLift f g a b hA hB hC hT hab i).comp (smallFstHom f g hA hB hC) =
      a.restrictSubspace (coneDomain f g a b i).carrier (coneDomain f g a b i).is_domain :=
  coneChartLift_comp_fst f g a b hab hA hB hC hT i.val _ _ _ _ _

theorem coneDomainLift_comp_snd (i : ConeDomainIndex f g a b) :
    (coneDomainLift f g a b hA hB hC hT hab i).comp (smallSndHom f g hA hB hC) =
      b.restrictSubspace (coneDomain f g a b i).carrier (coneDomain f g a b i).is_domain :=
  coneChartLift_comp_snd f g a b hab hA hB hC hT i.val _ _ _ _ _

/-- Entire local maps agree on the actual intersection domains by strict
joint uniqueness of the two complete projections. -/
theorem coneDomainLift_overlap (i j : ConeDomainIndex f g a b) :
    (coneDomainLift f g a b hA hB hC hT hab i).restrictOriginalDomain
        (inf_le_left : coneDomain f g a b i ⊓ coneDomain f g a b j ≤ coneDomain f g a b i) =
      (coneDomainLift f g a b hA hB hC hT hab j).restrictOriginalDomain
        (inf_le_right : coneDomain f g a b i ⊓ coneDomain f g a b j ≤ coneDomain f g a b j) := by
  apply smallHom_ext f g hA hB hC
  · rw [← CompatibleStrongHom.restrictOriginalDomain_comp,
      ← CompatibleStrongHom.restrictOriginalDomain_comp,
      coneDomainLift_comp_fst, coneDomainLift_comp_fst,
      CompatibleStrongHom.restrictSubspace_restrictOriginalDomain,
      CompatibleStrongHom.restrictSubspace_restrictOriginalDomain]
  · rw [← CompatibleStrongHom.restrictOriginalDomain_comp,
      ← CompatibleStrongHom.restrictOriginalDomain_comp,
      coneDomainLift_comp_snd, coneDomainLift_comp_snd,
      CompatibleStrongHom.restrictSubspace_restrictOriginalDomain,
      CompatibleStrongHom.restrictSubspace_restrictOriginalDomain]

/-- The full local cone lifts form an actual full strong matching family. -/
def coneDomainMatchingFamily :
    OriginalDomainStrongMatchingFamily T (smallPresentation f g hA hB hC) (coneDomain f g a b) where
  localMap i := (coneDomainLift f g a b hA hB hC hT hab i).toStrongHom
  overlap i j := congrArg CompatibleStrongHom.toStrongHom
    (coneDomainLift_overlap f g a b hA hB hC hT hab i j)

/-- Construct the actual original source selection from the local cone domains. -/
def coneSourceSelection : T.atlas.RefiningSelection :=
  domainCoverSourceSelection (coneDomain f g a b)
    (coneDomain_locallyRefines f g a b hT hA hB hab)

/-- The constructed source refinement and full compatible local matching
family give an actual complete strong cone lift. -/
def refinedConeLift :
    CompatibleStrongHom (T.refiningSubpresentation (coneSourceSelection f g a b hA hB hT hab))
      (smallPresentation f g hA hB hC) :=
  (coneDomainMatchingFamily f g a b hA hB hC hT hab).compatibleRefinedGlue hT
    (coneDomain_locallyRefines f g a b hT hA hB hab)

/-- The first complete projection recovers the ambient cone leg on the
actual selected source atlas. -/
theorem refinedConeLift_comp_fst :
    (refinedConeLift f g a b hA hB hC hT hab).comp (smallFstHom f g hA hB hC) =
      a.restrictSubatlasSource (coneSourceSelection f g a b hA hB hT hab).carrier
        (coneSourceSelection f g a b hA hB hT hab).locally_refining := by
  apply OriginalDomainStrongMatchingFamily.compatibleRefinedGlue_comp
  intro i
  exact coneDomainLift_comp_fst f g a b hA hB hC hT hab i

/-- The second complete projection recovers the other full cone leg. -/
theorem refinedConeLift_comp_snd :
    (refinedConeLift f g a b hA hB hC hT hab).comp (smallSndHom f g hA hB hC) =
      b.restrictSubatlasSource (coneSourceSelection f g a b hA hB hT hab).carrier
        (coneSourceSelection f g a b hA hB hT hab).locally_refining := by
  apply OriginalDomainStrongMatchingFamily.compatibleRefinedGlue_comp
  intro i
  exact coneDomainLift_comp_snd f g a b hA hB hC hT hab i

end Langlands.Analytic.FibreProduct
