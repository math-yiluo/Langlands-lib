import Langlands.Geometry.Analytic.AffineAnalytificationAffinoidMap
import Langlands.Geometry.Analytic.CompatibleStrongOriginalRestriction
import Langlands.Geometry.Analytic.DirectedAtlasReconstruction

/-! # Algebra maps on the charts of a saturated source -/

noncomputable section

universe u v w x

namespace Langlands.Analytic.AffineAnalytification

open CategoryTheory Set AffinoidAtlasPresentation PresentedAffinoidAlgebra

namespace ChartFamilyComparison

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- The bounded identity transported along equality of presented algebras. -/
def algebraCast {R S : PresentedAffinoidAlgebra K} (h : R = S) : BoundedAlgHom K R S := by
  subst S
  exact BoundedAlgHom.id K R

@[simp]
theorem algebraCast_rfl (R : PresentedAffinoidAlgebra K) :
    algebraCast (rfl : R = R) = BoundedAlgHom.id K R := rfl

/-- Heterogeneous equality of bounded maps gives the commuting cast square. -/
theorem algebraCast_square {R R' S S' : PresentedAffinoidAlgebra K}
    (hR : R = R') (hS : S = S')
    {f : BoundedAlgHom K S R} {g : BoundedAlgHom K S' R'} (h : HEq f g) :
    (algebraCast hR).comp f = g.comp (algebraCast hS) := by
  cases hR
  cases hS
  cases eq_of_heq h
  simp only [algebraCast_rfl, BoundedAlgHom.id_comp, BoundedAlgHom.comp_id]

@[simp]
theorem algebraCast_comp_symm {R S : PresentedAffinoidAlgebra K} (h : R = S) :
    (algebraCast h).comp (algebraCast h.symm) = BoundedAlgHom.id K S := by
  cases h
  exact BoundedAlgHom.id_comp _

variable [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)

omit [CompleteSpace K] in
private theorem coordinate_triangle {R Q T : PresentedAffinoidAlgebra K}
    (f : BoundedAlgHom K R T) (r : BoundedAlgHom K Q R) (g : BoundedAlgHom K Q T)
    (a : A →ₐ[K] Q) (b : A →ₐ[K] R)
    (hc : r.toAlgHom.comp a = b) (hg : g = f.comp r) :
    f.toAlgHom.comp b = g.toAlgHom.comp a := by
  rw [hg, ← hc]
  rfl

omit [CompleteSpace K] in
private theorem coordinate_square {R R' Q Q' : PresentedAffinoidAlgebra K}
    (s : BoundedAlgHom K R' R) (f : BoundedAlgHom K Q R)
    (g : BoundedAlgHom K Q' R') (t : BoundedAlgHom K Q' Q)
    (a : A →ₐ[K] Q) (b : A →ₐ[K] Q')
    (hf : s.comp g = f.comp t) (hc : t.toAlgHom.comp b = a) :
    s.toAlgHom.comp (g.toAlgHom.comp b) = f.toAlgHom.comp a := by
  rw [← hc]
  exact congrArg (fun h : BoundedAlgHom K Q' R => h.toAlgHom.comp b) hf

/-- Directedness with the presentation's literal index type. -/
theorem original_hasDirectedCharts : (presentation K P).atlas.HasDirectedCharts :=
  atlas_hasDirectedCharts K P

/-- The coordinate-algebra map with the presentation's literal chart algebra. -/
def coordinateMap (j : (presentation K P).atlas.Index) :
    A →ₐ[K] (presentation K P).atlas.algebra j :=
  PolynomialLocus.algebraMap P (AnalyticAffineSpace.polyradius K P.arity j.val)

/-- Restriction preserves every coordinate-algebra element. -/
theorem restriction_coordinateMap (j j' : (presentation K P).atlas.Index)
    (h : range ((presentation K P).atlas.chart j) ⊆
      range ((presentation K P).atlas.chart j')) :
    ((presentation K P).atlas.restriction j j' h).toAlgHom.comp (coordinateMap P j') =
      coordinateMap P j := by
  ext a
  exact PolynomialLocus.restriction_algebraMap P _ _ _ a

/-- The original polynomial chart, as an index of its saturation. -/
abbrev originalIndex (j : (presentation K P).atlas.Index) :
    (saturated K P).presentation.atlas.Index :=
  (presentation K P).atlas.originalSaturatedIndex j

/-- The original algebra in a saturated original chart is unchanged up to equality. -/
theorem originalAlgebra (j : (presentation K P).atlas.Index) :
    (saturated K P).presentation.atlas.algebra (originalIndex P j) =
      (presentation K P).atlas.algebra j :=
  (presentation K P).atlas.saturatedAtlas_original_algebra j

/-- Chart ranges of original charts are unchanged in the saturation. -/
theorem originalRange (j : (presentation K P).atlas.Index) :
    range ((saturated K P).presentation.atlas.chart (originalIndex P j)) =
      range ((presentation K P).atlas.chart j) :=
  (presentation K P).atlas.saturatedAtlas_original_range j

/-- Original chart containments persist in the saturation. -/
theorem originalSubset (j j' : (presentation K P).atlas.Index)
    (h : range ((presentation K P).atlas.chart j) ⊆
      range ((presentation K P).atlas.chart j')) :
    range ((saturated K P).presentation.atlas.chart (originalIndex P j)) ⊆
      range ((saturated K P).presentation.atlas.chart (originalIndex P j')) := by
  rw [originalRange, originalRange]
  exact h

/-- The bounded casts intertwine every original atlas restriction. -/
theorem originalRestriction_cast (j j' : (presentation K P).atlas.Index)
    (h : range ((presentation K P).atlas.chart j) ⊆
      range ((presentation K P).atlas.chart j')) :
    ((saturated K P).presentation.atlas.restriction (originalIndex P j)
        (originalIndex P j') (originalSubset P j j' h)).comp
      (algebraCast (originalAlgebra P j').symm) =
    (algebraCast (originalAlgebra P j).symm).comp
      ((presentation K P).atlas.restriction j j' h) := by
  exact (algebraCast_square (originalAlgebra P j).symm (originalAlgebra P j').symm
    ((presentation K P).atlas.saturatedAtlas_original_restriction_heq j j' h _).symm).symm

/-- Saturation of a directed atlas still has directed charts. -/
theorem saturated_hasDirectedCharts : (saturated K P).presentation.atlas.HasDirectedCharts := by
  intro S T
  let a := (presentation K P).atlas
  let i := (a.saturatedRepresentative S).index
  let j := (a.saturatedRepresentative T).index
  obtain ⟨q, hiq, hjq⟩ := original_hasDirectedCharts P i j
  refine ⟨originalIndex P q, ?_, ?_⟩
  · rw [originalRange]
    rintro _ ⟨x, rfl⟩
    exact hiq ⟨(a.saturatedRepresentative S).domain.spectrumMap x, rfl⟩
  · rw [originalRange]
    rintro _ ⟨x, rfl⟩
    exact hjq ⟨(a.saturatedRepresentative T).domain.spectrumMap x, rfl⟩

variable {S : SaturatedAtlasPresentation.{u, u, u} K}

/-- Admissibility for an original polynomial chart, expressed in the saturation. -/
theorem original_admissible (F : S ⟶ saturated K P) (i : S.presentation.atlas.Index)
    (j : (presentation K P).atlas.Index)
    (h : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j)) :
    F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((saturated K P).presentation.atlas.chart (originalIndex P j)) := by
  rw [originalRange]
  exact h

/-- Every source chart maps into an original polynomial chart. -/
theorem original_target_exists (F : S ⟶ saturated K P) (i : S.presentation.atlas.Index) :
    ∃ j : (presentation K P).atlas.Index,
      F.baseMap '' range (S.presentation.atlas.chart i) ⊆
        range ((presentation K P).atlas.chart j) := by
  obtain ⟨T, hT⟩ := F.target_exists i
  let a := (presentation K P).atlas
  refine ⟨(a.saturatedRepresentative T).index, hT.trans ?_⟩
  rintro _ ⟨x, rfl⟩
  exact ⟨(a.saturatedRepresentative T).domain.spectrumMap x, rfl⟩

/-- Pullback from an original polynomial chart, with its literal original algebra. -/
def originalPullback (F : S ⟶ saturated K P) (i : S.presentation.atlas.Index)
    (j : (presentation K P).atlas.Index)
    (h : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j)) :
    BoundedAlgHom K ((presentation K P).atlas.algebra j) (S.presentation.atlas.algebra i) :=
  (F.pullback i (originalIndex P j) (original_admissible P F i j h)).comp
    (algebraCast (originalAlgebra P j).symm)

/-- Naturality holds with the original polynomial restrictions and source restrictions. -/
theorem originalPullback_naturality (F : S ⟶ saturated K P)
    (i i' : S.presentation.atlas.Index) (j j' : (presentation K P).atlas.Index)
    (hi : range (S.presentation.atlas.chart i) ⊆ range (S.presentation.atlas.chart i'))
    (hj : range ((presentation K P).atlas.chart j) ⊆
      range ((presentation K P).atlas.chart j'))
    (h : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j))
    (h' : F.baseMap '' range (S.presentation.atlas.chart i') ⊆
      range ((presentation K P).atlas.chart j')) :
    (S.presentation.atlas.restriction i i' hi).comp (originalPullback P F i' j' h') =
      (originalPullback P F i j h).comp ((presentation K P).atlas.restriction j j' hj) := by
  unfold originalPullback
  rw [← BoundedAlgHom.comp_assoc, F.restriction_comm i i' (originalIndex P j)
    (originalIndex P j') hi (originalSubset P j j' hj),
    BoundedAlgHom.comp_assoc, originalRestriction_cast]
  exact (BoundedAlgHom.comp_assoc _ _ _).symm

/-- A compatible family of algebra maps on every original source chart. -/
structure AlgebraFamily (S : AffinoidAtlasPresentation.{u, u, u} K)
    (A : Type v) [CommRing A] [Algebra K A] where
  map : ∀ i, A →ₐ[K] S.atlas.algebra i
  naturality : ∀ i i' (hi : range (S.atlas.chart i) ⊆ range (S.atlas.chart i')),
    (S.atlas.restriction i i' hi).toAlgHom.comp (map i') = map i

/-- Select an original polynomial target for each source chart. -/
def selectedTarget (F : S ⟶ saturated K P) (i : S.presentation.atlas.Index) :
    (presentation K P).atlas.Index :=
  (original_target_exists P F i).choose

theorem selectedTarget_spec (F : S ⟶ saturated K P) (i : S.presentation.atlas.Index) :
    F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart (selectedTarget P F i)) :=
  (original_target_exists P F i).choose_spec

/-- The algebra map read from a source chart and any admissible original target. -/
def chartAlgHom (F : S ⟶ saturated K P) (i : S.presentation.atlas.Index)
    (j : (presentation K P).atlas.Index)
    (h : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j)) : A →ₐ[K] S.presentation.atlas.algebra i :=
  (originalPullback P F i j h).toAlgHom.comp (coordinateMap P j)

/-- Target enlargement preserves the bounded map after restriction. -/
theorem originalPullback_upper (F : S ⟶ saturated K P) (i : S.presentation.atlas.Index)
    (j q : (presentation K P).atlas.Index)
    (hj : range ((presentation K P).atlas.chart j) ⊆
      range ((presentation K P).atlas.chart q))
    (h : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j))
    (hq : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart q)) :
    originalPullback P F i q hq = (originalPullback P F i j h).comp
      ((presentation K P).atlas.restriction j q hj) := by
  calc
    originalPullback P F i q hq =
        (BoundedAlgHom.id K (S.presentation.atlas.algebra i)).comp
          (originalPullback P F i q hq) := (BoundedAlgHom.id_comp _).symm
    _ = (S.presentation.atlas.restriction i i Subset.rfl).comp
        (originalPullback P F i q hq) :=
      congrArg (fun r : BoundedAlgHom K (S.presentation.atlas.algebra i)
          (S.presentation.atlas.algebra i) => r.comp (originalPullback P F i q hq))
        (S.presentation.atlas.restriction_id i Subset.rfl).symm
    _ = _ := originalPullback_naturality P F i i j q Subset.rfl hj h hq

/-- Enlarging an admissible target leaves its coordinate-algebra map unchanged. -/
theorem chartAlgHom_upper (F : S ⟶ saturated K P) (i : S.presentation.atlas.Index)
    (j q : (presentation K P).atlas.Index)
    (hj : range ((presentation K P).atlas.chart j) ⊆
      range ((presentation K P).atlas.chart q))
    (h : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j))
    (hq : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart q)) :
    chartAlgHom P F i j h = chartAlgHom P F i q hq := by
  exact coordinate_triangle (originalPullback P F i j h)
    ((presentation K P).atlas.restriction j q hj) (originalPullback P F i q hq)
    (coordinateMap P q) (coordinateMap P j)
    (restriction_coordinateMap P j q hj)
    (originalPullback_upper P F i j q hj h hq)

/-- The coordinate-algebra map is independent of the admissible target chart. -/
theorem chartAlgHom_independent (F : S ⟶ saturated K P) (i : S.presentation.atlas.Index)
    (j j' : (presentation K P).atlas.Index)
    (h : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j))
    (h' : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j')) :
    chartAlgHom P F i j h = chartAlgHom P F i j' h' := by
  obtain ⟨q, hjq, hj'q⟩ := original_hasDirectedCharts P j j'
  have hq := h.trans hjq
  exact (chartAlgHom_upper P F i j q hjq h hq).trans
    (chartAlgHom_upper P F i j' q hj'q h' hq).symm

/-- The coordinate-algebra maps preserve every source restriction. -/
theorem chartAlgHom_naturality (F : S ⟶ saturated K P)
    (i i' : S.presentation.atlas.Index) (j j' : (presentation K P).atlas.Index)
    (hi : range (S.presentation.atlas.chart i) ⊆ range (S.presentation.atlas.chart i'))
    (hj : range ((presentation K P).atlas.chart j) ⊆
      range ((presentation K P).atlas.chart j'))
    (h : F.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j))
    (h' : F.baseMap '' range (S.presentation.atlas.chart i') ⊆
      range ((presentation K P).atlas.chart j')) :
    (S.presentation.atlas.restriction i i' hi).toAlgHom.comp (chartAlgHom P F i' j' h') =
      chartAlgHom P F i j h :=
  coordinate_square (S.presentation.atlas.restriction i i' hi)
    (originalPullback P F i j h) (originalPullback P F i' j' h')
    ((presentation K P).atlas.restriction j j' hj) (coordinateMap P j) (coordinateMap P j')
    (originalPullback_naturality P F i i' j j' hi hj h h')
    (restriction_coordinateMap P j j' hj)

/-- Read the compatible algebra family of a complete strong morphism. -/
def toAlgebraFamily (F : S ⟶ saturated K P) : AlgebraFamily S.presentation A where
  map i := chartAlgHom P F i (selectedTarget P F i) (selectedTarget_spec P F i)
  naturality i i' hi := by
    let j := selectedTarget P F i
    let j' := selectedTarget P F i'
    obtain ⟨q, hjq, hj'q⟩ := original_hasDirectedCharts P j j'
    have hq := (selectedTarget_spec P F i).trans hjq
    have hq' := (selectedTarget_spec P F i').trans hj'q
    exact (congrArg
      (fun φ : A →ₐ[K] S.presentation.atlas.algebra i' =>
        (S.presentation.atlas.restriction i i' hi).toAlgHom.comp φ)
      (chartAlgHom_independent P F i' j' q (selectedTarget_spec P F i') hq')).trans
      ((chartAlgHom_naturality P F i i' q q hi Subset.rfl hq hq').trans
        (chartAlgHom_independent P F i j q (selectedTarget_spec P F i) hq).symm)

end ChartFamilyComparison

end Langlands.Analytic.AffineAnalytification
