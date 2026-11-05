import Langlands.Geometry.Analytic.SpecialChartCover
import Langlands.Geometry.Analytic.FiniteChartHausdorffComparison
import Langlands.Geometry.Analytic.FiniteChartOriginalRecognition

/-! # Actual Banach sections and canonical restrictions on special subsets -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Literal special subsets of the given original atlas. -/
abbrev SpecialSubset := {W : Set X // a.IsSpecialSet W}

namespace SpecialSubset

variable {a} (W : a.SpecialSubset)

/-- Choose an actual finite special covering already witnessed by
specialness; its section algebra is constructed below from this family. -/
def gluingData : FiniteChartGluingData a := W.property.choose

theorem gluingData_locus : W.gluingData.locus = W.val := W.property.choose_spec.1

theorem gluingData_isSpecial : W.gluingData.IsSpecialCover := W.property.choose_spec.2

instance : T2Space W.gluingData.locus := W.gluingData_isSpecial.1

/-- The actual closed finite-product equalizer associated to a witnessed
special cover, with its inherited norm and algebra operations. -/
abbrev SectionAlgebra := W.gluingData.SectionAlgebra

instance : CompleteSpace W.SectionAlgebra :=
  inferInstanceAs (CompleteSpace W.gluingData.SectionAlgebra)

instance : IsUltrametricDist W.SectionAlgebra :=
  inferInstanceAs (IsUltrametricDist W.gluingData.SectionAlgebra)

/-- The canonical continuous map from the unchanged literal special
subspace to the spectrum of its constructed Banach section algebra. -/
def spectrumMap : C(W.val, BanachSpectrum W.SectionAlgebra) where
  toFun x := W.gluingData.spectrumMap ((Homeomorph.setCongr W.gluingData_locus).symm x)
  continuous_toFun := W.gluingData.continuous_spectrumMap.comp
    (Homeomorph.setCongr W.gluingData_locus).symm.continuous

variable (U V : a.SpecialSubset)

theorem gluingData_subset (h : U.val ⊆ V.val) :
    U.gluingData.locus ⊆ V.gluingData.locus := by
  intro x hx
  exact V.gluingData_locus.symm ▸ h (U.gluingData_locus ▸ hx)

/-- A literal inclusion constructs the actual bounded contravariant
restriction without any supplied original-chart subordinate cover. -/
def restriction (h : U.val ⊆ V.val) :
    BoundedAlgHom K V.SectionAlgebra U.SectionAlgebra :=
  V.gluingData.restrictionTo U.gluingData (U.gluingData_subset V h)

@[simp]
theorem restriction_self :
    W.restriction W Subset.rfl = BoundedAlgHom.id K W.SectionAlgebra :=
  W.gluingData.restrictionTo_self

/-- Restricting along two nested literal special subsets agrees with the
single direct restriction as an entire bounded algebra map. -/
theorem restriction_comp (hUV : U.val ⊆ V.val) (hVW : V.val ⊆ W.val) :
    (U.restriction V hUV).comp (V.restriction W hVW) =
      U.restriction W (hUV.trans hVW) :=
  W.gluingData.restrictionTo_comp V.gluingData U.gluingData
    (V.gluingData_subset W hVW) (U.gluingData_subset V hUV)

/-- The actual section restriction and literal inclusion identify the
canonical spectrum maps on every point of the smaller special subset. -/
theorem comap_spectrumMap (h : U.val ⊆ V.val) (x : U.val) :
    BanachSpectrum.comap (U.restriction V h).toBoundedRingHom (U.spectrumMap x) =
      V.spectrumMap ⟨x.val, h x.property⟩ :=
  V.gluingData.comap_spectrumMap_restrictionTo U.gluingData
    (U.gluingData_subset V h) ((Homeomorph.setCongr U.gluingData_locus).symm x)

/-- Every other finite original-chart defining family for the same
literal set gives an actually constructed bounded equivalent algebra. -/
def comparisonEquiv (d : FiniteChartGluingData a) (hd : d.locus = W.val) :
    BoundedAlgEquiv K W.SectionAlgebra d.SectionAlgebra :=
  W.gluingData.sectionAlgEquivOfLocusEq d (W.gluingData_locus.trans hd.symm)

/-- The comparison identifies the actual point maps over the same ambient
points, with the contravariant spectrum direction. -/
theorem comparisonEquiv_spectrumMap (d : FiniteChartGluingData a)
    (hd : d.locus = W.val) (x : d.locus) :
    (W.comparisonEquiv d hd).spectrumHomeomorph (d.spectrumMap x) =
      W.spectrumMap ⟨x.val, hd ▸ x.property⟩ :=
  W.gluingData.sectionAlgEquivOfLocusEq_spectrumMap d
    (W.gluingData_locus.trans hd.symm) x

variable (a)

/-- Each original chart gives a literal special subset by the constructed
singleton special covering. -/
def original (parent : a.Index) : a.SpecialSubset :=
  ⟨Set.range (a.chart parent), a.isSpecialSet_chart_range parent⟩

/-- Even though the witnessed special covering was chosen independently,
its sections recover the entire unchanged original chart algebra. -/
def originalAlgebraEquiv (parent : a.Index) :
    BoundedAlgEquiv K (a.algebra parent) (original a parent).SectionAlgebra :=
  (original a parent).gluingData.parentAlgEquiv parent
    (original a parent).gluingData_locus

/-- On each original spectrum the canonical special-subset map is exactly
the map induced by the constructed bounded original-algebra equivalence. -/
theorem original_spectrumMap (parent : a.Index) (x : BanachSpectrum (a.algebra parent)) :
    (originalAlgebraEquiv a parent).spectrumHomeomorph.symm x =
      (original a parent).spectrumMap ⟨a.chart parent x, Set.mem_range_self x⟩ := by
  let d := (original a parent).gluingData
  let hd := (original a parent).gluingData_locus
  let y : d.locus := (Homeomorph.setCongr hd).symm
    ⟨a.chart parent x, Set.mem_range_self x⟩
  have hy : d.parentHomeomorph parent hd y = x :=
    (a.isEmbedding_chart parent).toHomeomorph.symm_apply_apply x
  exact (congrArg (d.parentAlgEquiv parent hd).spectrumHomeomorph.symm hy).symm.trans
    (d.spectrumMap_eq_parent parent hd y).symm

end SpecialSubset

end Langlands.Analytic.IndexedAffinoidAtlas
