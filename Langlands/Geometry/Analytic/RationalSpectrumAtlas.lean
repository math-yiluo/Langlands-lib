import Langlands.Geometry.Analytic.DisjointAffinoidAtlas
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomain
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartIntersection
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartTerminal

/-! # An actual rational-domain atlas on each presented affinoid spectrum -/

noncomputable section

universe u

namespace Langlands.Analytic.RationalSpectrumAtlas

open CategoryTheory Set Topology
open PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K}

/-- Literal rational loci, so repeated presentations do not repeat a domain. -/
def Index (K : Type u) [NormedField K] [IsUltrametricDist K]
    (A : PresentedAffinoidAlgebra K) :=
  {U : Set (BanachSpectrum A) // ∃ d : RationalChart K A, d.locus = U}

namespace Index

/-- The index supplied by any actual positive-radius rational presentation. -/
def ofChart (d : RationalChart K A) : Index K A := ⟨d.locus, d, rfl⟩

/-- A chosen actual quotient presentation of this literal locus. -/
def presentation (i : Index K A) : RationalChart K A := i.property.choose

@[simp]
theorem locus_presentation (i : Index K A) : i.presentation.locus = i.val :=
  i.property.choose_spec

/-- Changing to the chosen representative retains the actual bounded algebra
comparison; no equality of quotient presentations is asserted. -/
def representativeIso [CompleteSpace K] (d : RationalChart K A) :
    d ≅ (ofChart d).presentation :=
  RationalChart.isoOfLocusEq d (ofChart d).presentation
    (locus_presentation (ofChart d)).symm

/-- An index for the whole spectrum, including the empty-spectrum case. -/
def whole : Index K A := ofChart (RationalChart.whole K A)

@[simp]
theorem val_whole : (whole : Index K A).val = Set.univ :=
  RationalChart.locus_whole K A

/-- The published all-products rational quotient realizes each intersection. -/
def inter (i j : Index K A) : Index K A :=
  ofChart (i.presentation.inter j.presentation)

@[simp]
theorem val_inter (i j : Index K A) : (i.inter j).val = i.val ∩ j.val := by
  change (i.presentation.inter j.presentation).locus = _
  rw [RationalChart.locus_inter, locus_presentation, locus_presentation]

end Index

/-- The family consists of all the actual rational loci over the fixed base. -/
def family (K : Type u) [NormedField K] [IsUltrametricDist K]
    (A : PresentedAffinoidAlgebra K) : Set (Set (BanachSpectrum A)) :=
  Set.range (fun i : Index K A => i.val)

theorem family_eq_range_locus :
    family K A = Set.range (fun d : RationalChart K A => d.locus) := by
  ext U
  constructor
  · rintro ⟨i, rfl⟩
    exact i.property
  · rintro ⟨d, rfl⟩
    exact ⟨Index.ofChart d, rfl⟩

theorem isNet_family : AtlasTopology.IsNet (family K A) := by
  refine ⟨AtlasTopology.isQuasinet_of_univ_mem
    ⟨Index.whole, Index.val_whole⟩, ?_⟩
  rintro U ⟨i, rfl⟩ V ⟨j, rfl⟩
  apply AtlasTopology.isQuasinet_of_univ_mem
  refine ⟨i.val ∩ j.val, ⟨i.inter j, Index.val_inter i j⟩, Subset.rfl, ?_⟩
  ext x
  exact iff_of_true (Set.mem_univ x) x.property

/-- The actual spectrum map of the chosen rational quotient. -/
def chart (i : Index K A) : BanachSpectrum i.presentation.algebra → BanachSpectrum A :=
  i.presentation.spectrumMap

@[simp]
theorem range_chart (i : Index K A) : Set.range (chart i) = i.val :=
  i.presentation.range_comap_baseMap.trans i.locus_presentation

theorem isEmbedding_chart (i : Index K A) : IsEmbedding (chart i) := by
  refine (i.presentation.spectrumMap.continuous.isClosedEmbedding ?_).isEmbedding
  intro x y h
  apply i.presentation.locusHomeomorph.injective
  exact Subtype.ext h

theorem chartDomain_injective :
    Function.Injective (fun i : Index K A => Set.range (chart i)) := by
  intro i j h
  apply Subtype.ext
  simpa only [range_chart] using h

variable [CompleteSpace K]

/-- The entire bounded restriction is constructed by full representation. -/
def restriction (i j : Index K A) (h : Set.range (chart i) ⊆ Set.range (chart j)) :
    BoundedAlgHom K j.presentation.algebra i.presentation.algebra :=
  (RationalChart.restrictionOfSubset i.presentation j.presentation (by
    simpa only [range_chart, Index.locus_presentation] using h)).restriction

theorem restriction_comp_baseMap (i j : Index K A)
    (h : Set.range (chart i) ⊆ Set.range (chart j)) :
    (restriction i j h).comp j.presentation.baseMap = i.presentation.baseMap :=
  (RationalChart.restrictionOfSubset i.presentation j.presentation _).comp_baseMap

theorem restriction_chart (i j : Index K A)
    (h : Set.range (chart i) ⊆ Set.range (chart j))
    (x : BanachSpectrum i.presentation.algebra) :
    chart j (BanachSpectrum.comap (restriction i j h).toBoundedRingHom x) =
      chart i x :=
  (RationalChart.restrictionOfSubset i.presentation j.presentation _).spectrumMap_over_base x

/-- Relative full factorization is derived from the two representations over
the base, with equality of entire bounded maps. -/
theorem restriction_universal (i j : Index K A)
    (h : Set.range (chart i) ⊆ Set.range (chart j))
    (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K j.presentation.algebra R)
    (hφ : ∀ x : BanachSpectrum R,
      chart j (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (chart i)) :
    ∃! ψ : BoundedAlgHom K i.presentation.algebra R,
      ψ.comp (restriction i j h) = φ := by
  have hbase : HasImageIn K (φ.comp j.presentation.baseMap) i.presentation.locus := by
    intro x
    have hx := hφ x
    rw [range_chart, ← i.locus_presentation] at hx
    exact hx
  obtain ⟨ψ, hψ, huniq⟩ := i.presentation.existsUnique_factorization R
    (φ.comp j.presentation.baseMap) hbase
  refine ⟨ψ, ?_, ?_⟩
  · apply RationalPresentation.hom_ext_base K A j.presentation.radii
      j.presentation.denominator j.presentation.numerators R j.presentation.generates
    change (ψ.comp (restriction i j h)).comp j.presentation.baseMap =
      φ.comp j.presentation.baseMap
    rw [BoundedAlgHom.comp_assoc, restriction_comp_baseMap, hψ]
  · intro ψ' hψ'
    apply huniq ψ'
    calc
      ψ'.comp i.presentation.baseMap =
          (ψ'.comp (restriction i j h)).comp j.presentation.baseMap := by
            rw [BoundedAlgHom.comp_assoc, restriction_comp_baseMap]
      _ = φ.comp j.presentation.baseMap := by rw [hψ']

theorem restriction_id (i : Index K A)
    (h : Set.range (chart i) ⊆ Set.range (chart i)) :
    restriction i i h = BoundedAlgHom.id K i.presentation.algebra := by
  exact congrArg RationalChart.Restriction.restriction
    (@Subsingleton.elim (RationalChart.Restriction i.presentation i.presentation) inferInstance
      (RationalChart.restrictionOfSubset i.presentation i.presentation _)
      (𝟙 i.presentation))

theorem restriction_comp (i j k : Index K A)
    (hij : Set.range (chart i) ⊆ Set.range (chart j))
    (hjk : Set.range (chart j) ⊆ Set.range (chart k))
    (hik : Set.range (chart i) ⊆ Set.range (chart k)) :
    restriction i k hik = (restriction i j hij).comp (restriction j k hjk) := by
  exact congrArg RationalChart.Restriction.restriction
    (@Subsingleton.elim (RationalChart.Restriction i.presentation k.presentation) inferInstance
      (RationalChart.restrictionOfSubset i.presentation k.presentation _)
      (RationalChart.restrictionOfSubset i.presentation j.presentation _ ≫
        RationalChart.restrictionOfSubset j.presentation k.presentation _))

/-- All rational quotient charts form a concrete affinoid atlas; all domain
and coherence obligations are proved from the published constructions. -/
def atlas (A : PresentedAffinoidAlgebra K) :
    IndexedAffinoidAtlas.{u, u, u} K (BanachSpectrum A) where
  Index := Index K A
  algebra i := i.presentation.algebra
  chart := chart
  isEmbedding_chart := isEmbedding_chart
  chartDomain_injective := chartDomain_injective
  locallyHausdorff _ := ⟨Set.univ, Filter.univ_mem, inferInstance⟩
  isNet_chartFamily := by
    simpa only [family, range_chart] using (isNet_family (K := K) (A := A))
  restriction := restriction
  restriction_chart := restriction_chart
  restriction_universal := restriction_universal
  restriction_id := restriction_id
  restriction_comp := restriction_comp

/-- The atlas contains precisely the supplied positive-radius rational loci. -/
theorem atlas_chartFamily :
    Set.range (fun i => Set.range ((atlas A).chart i)) =
      Set.range (fun d : RationalChart K A => d.locus) := by
  change Set.range (fun i : Index K A => Set.range (chart i)) = _
  simpa only [family, range_chart] using (family_eq_range_locus (K := K) (A := A))

/-- Each rational domain is a literal chart of the constructed atlas. -/
theorem atlas_ofChart_range (d : RationalChart K A) :
    Set.range ((atlas A).chart (Index.ofChart d)) = d.locus :=
  range_chart (Index.ofChart d)

/-- The chosen whole-locus representative is a greatest chart. -/
theorem atlas_whole_range :
    Set.range ((atlas A).chart Index.whole) = Set.univ := by
  change Set.range (chart (Index.whole : Index K A)) = Set.univ
  exact (range_chart _).trans Index.val_whole

end Langlands.Analytic.RationalSpectrumAtlas
