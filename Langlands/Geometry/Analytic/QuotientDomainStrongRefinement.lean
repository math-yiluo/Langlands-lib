import Langlands.Geometry.Analytic.QuotientStrongDomainLocalization
import Langlands.Geometry.Analytic.OriginalDomainCoverSelection

/-! # Full strong refinement of arbitrary quotient-domain matching families -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.SaturatedAtlasPresentation.SourceCategory

open CategoryTheory Set AffinoidAtlasPresentation
open IndexedAffinoidAtlas.OriginalChartDomain
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K} {ι : Type z}

/-- Actual quotient arrows on original domains, agreeing on their actual
intersections. No strong representatives or global arrow are input data. -/
structure QuotientDomainMatchingFamily
    (A B : SaturatedAtlasPresentation.{u, v, w} K)
    (D : ι → A.presentation.atlas.OriginalChartDomain) where
  localMap : ∀ k, ofPresentation (A.originalDomain (D k)) ⟶ ofPresentation B
  overlap : ∀ k l,
    domainMap (inf_le_left : D k ⊓ D l ≤ D k) ≫ localMap k =
      domainMap (inf_le_right : D k ⊓ D l ≤ D l) ≫ localMap l

namespace QuotientDomainMatchingFamily

variable {D : ι → A.presentation.atlas.OriginalChartDomain}

/-- The input overlap equation restricts to every smaller common domain. -/
theorem restrict_eq (d : QuotientDomainMatchingFamily A B D)
    (k l : ι) {S : A.presentation.atlas.OriginalChartDomain}
    (hSk : S ≤ D k) (hSl : S ≤ D l) :
    domainMap hSk ≫ d.localMap k = domainMap hSl ≫ d.localMap l := by
  calc
    domainMap hSk ≫ d.localMap k =
        domainMap (le_inf hSk hSl) ≫
          (domainMap (inf_le_left : D k ⊓ D l ≤ D k) ≫ d.localMap k) := by
      erw [← Category.assoc, domainMap_comp]
    _ = domainMap (le_inf hSk hSl) ≫
          (domainMap (inf_le_right : D k ⊓ D l ≤ D l) ≫ d.localMap l) :=
      congrArg (fun f => domainMap (le_inf hSk hSl) ≫ f) (d.overlap k l)
    _ = domainMap hSl ≫ d.localMap l := by
      erw [← Category.assoc, domainMap_comp]

/-- Choose the proved whole-chart strong representation of each local arrow. -/
def chartData (d : QuotientDomainMatchingFamily A B D) (k : ι) :
    ChartRepresentation (d.localMap k) :=
  chartRepresentation (d.localMap k)

/-- Retain both the original covering member and its selected original chart. -/
def RefinementIndex (d : QuotientDomainMatchingFamily A B D) :
    Type (max z w) :=
  Σ k : ι, {i : (A.originalDomain (D k)).presentation.atlas.Index //
    i ∈ (d.chartData k).selection}

/-- The actual ambient domain underlying a selected local chart. -/
def refinementDomain (d : QuotientDomainMatchingFamily A B D)
    (t : d.RefinementIndex) : A.presentation.atlas.OriginalChartDomain :=
  (D t.1).subspaceExtend (ofChart t.2.val)

theorem refinementDomain_le (d : QuotientDomainMatchingFamily A B D)
    (t : d.RefinementIndex) : d.refinementDomain t ≤ D t.1 :=
  (D t.1).subspaceExtend_le (ofChart t.2.val)

/-- The refined domain is exactly the range of the original ambient chart. -/
theorem refinementDomain_carrier (d : QuotientDomainMatchingFamily A B D)
    (t : d.RefinementIndex) :
    (d.refinementDomain t).carrier =
      Set.range (A.presentation.atlas.chart t.2.val.val) := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨_, ⟨y, rfl⟩, rfl⟩

/-- Transport the complete local strong map to its ambient domain presentation. -/
def refinementMap (d : QuotientDomainMatchingFamily A B D)
    (t : d.RefinementIndex) : A.originalDomain (d.refinementDomain t) ⟶ B :=
  StrongHom.fromNestedOriginalDomain (A := A.presentation) (B := B.presentation)
    (D t.1) (ofChart t.2.val) ((d.chartData t.1).localMap t.2)

/-- The transported full map represents precisely the given quotient
restriction to the refined ambient domain. -/
theorem refinementMap_represents (d : QuotientDomainMatchingFamily A B D)
    (t : d.RefinementIndex) :
    domainMap (d.refinementDomain_le t) ≫ d.localMap t.1 =
      strongFunctor.map (d.refinementMap t) := by
  change domainMap ((D t.1).subspaceExtend_le (ofChart t.2.val)) ≫ _ = _
  erw [← domainNestedMap_inclusion, Category.assoc,
    (d.chartData t.1).represents t.2, domainNestedMap_comp_strong]
  rfl

/-- Equality of quotient restrictions implies equality of all full strong
bounded maps, by the proved faithful strong-map functor. -/
theorem refinementMap_overlap (d : QuotientDomainMatchingFamily A B D)
    (t s : d.RefinementIndex) :
    (d.refinementMap t).restrictOriginalDomain
        (inf_le_left : d.refinementDomain t ⊓ d.refinementDomain s ≤
          d.refinementDomain t) =
      (d.refinementMap s).restrictOriginalDomain
        (inf_le_right : d.refinementDomain t ⊓ d.refinementDomain s ≤
          d.refinementDomain s) := by
  have h :
      domainMap (inf_le_left : d.refinementDomain t ⊓ d.refinementDomain s ≤
        d.refinementDomain t) ≫ strongFunctor.map (d.refinementMap t) =
      domainMap (inf_le_right : d.refinementDomain t ⊓ d.refinementDomain s ≤
        d.refinementDomain s) ≫ strongFunctor.map (d.refinementMap s) := by
    erw [← d.refinementMap_represents t, ← d.refinementMap_represents s,
      ← Category.assoc, domainMap_comp, ← Category.assoc, domainMap_comp]
    exact d.restrict_eq t.1 s.1
      (inf_le_left.trans (d.refinementDomain_le t))
      (inf_le_right.trans (d.refinementDomain_le s))
  exact strongFunctor_map_injective (A := A.originalDomain
    (d.refinementDomain t ⊓ d.refinementDomain s)) (B := B)
    ((domainMap_comp_strong (A := A) (B := B) inf_le_left
      (d.refinementMap t)).symm.trans
      (h.trans (domainMap_comp_strong (A := A) (B := B) inf_le_right
        (d.refinementMap s))))

/-- An actual literal full strong matching family, constructed from arbitrary
quotient matching arrows rather than supplied as a strictness hypothesis. -/
def strongRefinement (d : QuotientDomainMatchingFamily A B D) :
    A.presentation.OriginalDomainStrongMatchingFamily B.presentation
      d.refinementDomain where
  localMap := d.refinementMap
  overlap := d.refinementMap_overlap

/-- The refined ambient charts supply finite relative neighborhoods in every
original covering member. This retains the entire quasinet condition. -/
theorem refinementDomain_locallyRefines (d : QuotientDomainMatchingFamily A B D) :
    AtlasTopology.LocallyRefines
      (Set.range (fun t => (d.refinementDomain t).carrier))
      (Set.range (fun k => (D k).carrier)) := by
  have h := IndexedAffinoidAtlas.domainCoverSelectionPredicate_locallyRefines
    D (fun k => (d.chartData k).selection)
  apply AtlasTopology.LocallyRefines.mono h ?_ Subset.rfl
  rintro _ ⟨i, rfl⟩
  obtain ⟨k, hi, hsel⟩ := i.property
  exact ⟨⟨k, ⟨⟨i.val, hi⟩, hsel⟩⟩, d.refinementDomain_carrier _⟩

/-- A quasinet domain cover remains a quasinet cover after the constructed
strong refinement. Empty domains and arbitrary family universes are allowed. -/
theorem strongRefinement_cover (d : QuotientDomainMatchingFamily A B D)
    (hD : AtlasTopology.LocallyRefines
      (Set.range (fun k => (D k).carrier)) {Set.univ}) :
    AtlasTopology.LocallyRefines
      (Set.range (fun t => (d.refinementDomain t).carrier)) {Set.univ} :=
  hD.trans d.refinementDomain_locallyRefines

/-- Each local selected-chart family is itself an actual whole-domain cover
of the corresponding original subspace presentation. -/
theorem chartData_cover (d : QuotientDomainMatchingFamily A B D) (k : ι) :
    AtlasTopology.LocallyRefines
      (Set.range (fun i : {i : (A.originalDomain (D k)).presentation.atlas.Index //
        i ∈ (d.chartData k).selection} => (ofChart i.val).carrier)) {Set.univ} := by
  have hq := ((A.originalDomain (D k)).presentation.atlas.isNet_selectedChartFamily
    (d.chartData k).selection.carrier (d.chartData k).selection.locally_refining).1
  intro U hU x _hx
  obtain rfl := Set.mem_singleton_iff.mp hU
  obtain ⟨σ, hf, hs, hm, hn⟩ := hq x
  exact ⟨σ, hf, hs, fun V hV => ⟨Set.subset_univ _, hm V hV⟩,
    by simpa only [nhdsWithin_univ] using hn⟩

end QuotientDomainMatchingFamily
end Langlands.Analytic.SaturatedAtlasPresentation.SourceCategory
