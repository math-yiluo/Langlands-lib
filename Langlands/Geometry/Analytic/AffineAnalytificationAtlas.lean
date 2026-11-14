import Langlands.Geometry.Analytic.AffineAnalytificationGluing
import Langlands.Geometry.Analytic.SaturatedStrongLocalization

/-! # The affinoid atlas of a finite polynomial locus -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffineAnalytification

open Set Topology PresentedAffinoidAlgebra

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] {A : Type v} [CommRing A] [Algebra K A]
  (P : FinitePolynomialPresentation K A)

/-- An original bounded chart as a full affinoid domain of a larger chart. -/
def chainDomain {m k : ℕ} (h : m ≤ k) : Domain K (algebra K P k) where
  algebra := algebra K P m
  baseMap := restriction K P h
  locus := range ((chartSystem K P).pull h)
  represents := represents_restriction K P h

theorem chainDomain_locus {m k : ℕ} (h : m ≤ k) :
    (chainDomain K P h).locus = chart K P k ⁻¹' range (chart K P m) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, (chart_pull K P h x).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, (isClosedEmbedding_chart K P k).injective ?_⟩
    exact (chart_pull K P h x).trans hx

/-- Repeated chart ranges have boundedly equivalent actual quotient algebras.
The equivalence is constructed from full domain representations over a common
larger chart, so it retains the algebra maps and nilpotents. -/
def equalRangeEquiv {m k : ℕ}
    (h : range (chart K P m) = range (chart K P k)) :
    BoundedAlgEquiv K (algebra K P m) (algebra K P k) :=
  Domain.boundedEquivOfLocusEq
    (chainDomain K P (le_max_left m k)) (chainDomain K P (le_max_right m k)) (by
      rw [chainDomain_locus, chainDomain_locus, h])

theorem equalRangeEquiv_comp_restriction {m k : ℕ}
    (h : range (chart K P m) = range (chart K P k)) :
    (equalRangeEquiv K P h).toBoundedAlgHom.comp
        (restriction K P (le_max_left m k)) =
      restriction K P (le_max_right m k) :=
  Domain.boundedEquivOfLocusEq_comp_baseMap _ _ _

theorem equalRangeEquiv_symm_comp_restriction {m k : ℕ}
    (h : range (chart K P m) = range (chart K P k)) :
    (equalRangeEquiv K P h).symm.toBoundedAlgHom.comp
        (restriction K P (le_max_right m k)) =
      restriction K P (le_max_left m k) :=
  Domain.boundedEquivOfLocusEq_symm_comp_baseMap _ _ _

theorem equalRangeEquiv_algebraMap {m k : ℕ}
    (h : range (chart K P m) = range (chart K P k)) (a : A) :
    equalRangeEquiv K P h
        (PolynomialLocus.algebraMap P (AnalyticAffineSpace.polyradius K P.arity m) a) =
      PolynomialLocus.algebraMap P (AnalyticAffineSpace.polyradius K P.arity k) a := by
  simpa only [BoundedAlgHom.comp_apply, restriction, PolynomialLocus.restriction_algebraMap,
    BoundedAlgEquiv.toBoundedAlgHom_apply] using
    congrArg (fun f : BoundedAlgHom K (algebra K P (max m k)) (algebra K P k) =>
      f (PolynomialLocus.algebraMap P
        (AnalyticAffineSpace.polyradius K P.arity (max m k)) a))
      (equalRangeEquiv_comp_restriction K P h)

/-- Keep the least original natural index for each distinct chart range. -/
def ChartIndex :=
  {m : ℕ // ∀ k, range (chart K P k) = range (chart K P m) → m ≤ k}

/-- The chosen original chart representing the range of the `m`-th chart. -/
def representative (m : ℕ) : ChartIndex K P :=
  ⟨Nat.find (show ∃ k, range (chart K P k) = range (chart K P m) from ⟨m, rfl⟩),
    by
      intro k hk
      exact Nat.find_min' _ (hk.trans (Nat.find_spec
        (show ∃ k, range (chart K P k) = range (chart K P m) from ⟨m, rfl⟩)))⟩

theorem range_representative (m : ℕ) :
    range (chart K P (representative K P m).val) = range (chart K P m) :=
  Nat.find_spec (show ∃ k, range (chart K P k) = range (chart K P m) from ⟨m, rfl⟩)

theorem representative_le (m : ℕ) : (representative K P m).val ≤ m :=
  Nat.find_min' _ rfl

/-- Recover the actual algebra of every original chart from its selected
representative by a bounded equivalence respecting the algebraic locus. -/
def representativeEquiv (m : ℕ) :
    BoundedAlgEquiv K (algebra K P (representative K P m).val) (algebra K P m) :=
  equalRangeEquiv K P (range_representative K P m)

theorem selected_chartDomain_injective :
    Function.Injective (fun i : ChartIndex K P => range (chart K P i.val)) := by
  intro i j h
  exact Subtype.ext (le_antisymm (i.property j.val h.symm) (j.property i.val h))

/-- On the selected original indices, every chart-range inclusion has the
same direction as the original radius restriction. -/
theorem selected_range_subset_iff (i j : ChartIndex K P) :
    range (chart K P i.val) ⊆ range (chart K P j.val) ↔ i.val ≤ j.val := by
  refine ⟨fun h => ?_, range_chart_mono K P⟩
  rcases le_total i.val j.val with hij | hji
  · exact hij
  · exact i.property j.val (Subset.antisymm (range_chart_mono K P hji) h)

theorem selected_isNet :
    AtlasTopology.IsNet
      (range (fun i : ChartIndex K P => range (chart K P i.val))) := by
  refine ⟨fun z => ?_, ?_⟩
  · obtain ⟨m, s, rfl⟩ := exists_chart K P z
    refine ⟨{range (chart K P (m + 1))}, Set.finite_singleton _, ?_, ?_, ?_⟩
    · rintro _ rfl
      exact ⟨representative K P (m + 1), range_representative K P (m + 1)⟩
    · rintro _ rfl
      exact range_chart_mono K P (Nat.le_succ m) ⟨s, rfl⟩
    · rw [Set.sUnion_singleton]
      exact range_chart_mem_nhds K P ⟨s, rfl⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    intro z
    have hW : range (chart K P (min i.val j.val)) ⊆
        range (chart K P i.val) ∩ range (chart K P j.val) :=
      subset_inter (range_chart_mono K P (min_le_left i.val j.val))
        (range_chart_mono K P (min_le_right i.val j.val))
    have hW' : range (chart K P i.val) ∩ range (chart K P j.val) ⊆
        range (chart K P (min i.val j.val)) := by
      rcases le_total i.val j.val with h | h
      · rw [min_eq_left h]
        exact inter_subset_left
      · rw [min_eq_right h]
        exact inter_subset_right
    refine ⟨{univ}, Set.finite_singleton _, ?_, ?_, ?_⟩
    · rintro _ rfl
      refine ⟨range (chart K P (min i.val j.val)),
        ⟨representative K P (min i.val j.val), range_representative K P _⟩, hW, ?_⟩
      ext w
      simp only [mem_univ, mem_preimage, true_iff]
      exact hW' w.property
    · rintro _ rfl
      trivial
    · rw [Set.sUnion_singleton]
      exact Filter.univ_mem

/-- The constructed atlas, with actual original quotient algebras and bounded
radius restrictions for all its chart-domain inclusions. -/
def atlas : IndexedAffinoidAtlas.{u, u, 0} K (Space K P) where
  Index := ChartIndex K P
  algebra i := algebra K P i.val
  chart i := chart K P i.val
  isEmbedding_chart i := (isClosedEmbedding_chart K P i.val).isEmbedding
  chartDomain_injective := selected_chartDomain_injective K P
  locallyHausdorff _ := ⟨univ, Filter.univ_mem, inferInstance⟩
  isNet_chartFamily := selected_isNet K P
  restriction i j h := restriction K P ((selected_range_subset_iff K P i j).1 h)
  restriction_chart i j h x := chart_pull K P ((selected_range_subset_iff K P i j).1 h) x
  restriction_universal i j h R φ hφ := by
    apply (represents_restriction K P ((selected_range_subset_iff K P i j).1 h)).2.2 R φ
    intro x
    obtain ⟨s, hs⟩ := hφ x
    refine ⟨s, (isClosedEmbedding_chart K P j.val).injective ?_⟩
    exact (chart_pull K P ((selected_range_subset_iff K P i j).1 h) s).trans hs
  restriction_id i _ := PolynomialLocus.restriction_self P _
  restriction_comp _ _ _ _ _ _ := PolynomialLocus.restriction_trans P _ _ _ _ _

theorem atlas_hasDirectedCharts : (atlas K P).HasDirectedCharts := by
  intro i j
  refine ⟨representative K P (max i.val j.val), ?_, ?_⟩
  · change range (chart K P i.val) ⊆ range (chart K P (representative K P _).val)
    rw [range_representative]
    exact range_chart_mono K P (le_max_left i.val j.val)
  · change range (chart K P j.val) ⊆ range (chart K P (representative K P _).val)
    rw [range_representative]
    exact range_chart_mono K P (le_max_right i.val j.val)

/-- The affine polynomial locus with its constructed affinoid atlas. -/
def presentation : AffinoidAtlasPresentation.{u, u, 0} K where
  space := TopCat.of (Space K P)
  atlas := atlas K P

/-- Saturation uses the Library's actual full local-domain construction. -/
def saturated : SaturatedAtlasPresentation.{u, u, u} K :=
  SaturatedAtlasPresentation.ofSaturation (presentation K P)

/-- The constructed affine analytification in the existing localized category. -/
def localized : SaturatedAtlasPresentation.LocalizedCategory.{u, u, u} (K := K) :=
  SaturatedAtlasPresentation.localizationFunctor.obj (saturated K P)

@[simp]
theorem saturated_space :
    (saturated K P).presentation.space = TopCat.of (Space K P) := rfl

@[simp]
theorem localized_space :
    SaturatedAtlasPresentation.localizedSpaceFunctor.obj (localized K P) =
      TopCat.of (Space K P) := rfl

end Langlands.Analytic.AffineAnalytification
