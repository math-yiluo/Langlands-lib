import Langlands.Geometry.Analytic.FieldValuedPoints
import Langlands.Geometry.Analytic.Spectrum.ResidueField.Functorial
import Langlands.Geometry.Analytic.ValuedField.IsometricDirectLimit

/-! # Compatible realization of one analytic point -/

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.PointField

open Set BanachSpectrum

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : AffinoidAtlasPresentation.{u, v, w} K) (x : A.space)

/-- Charts containing the point, ordered towards smaller domains. -/
structure Chart where
  index : A.atlas.Index
  contains : x ∈ range (A.atlas.chart index)

instance : Preorder (Chart A x) where
  le i j := range (A.atlas.chart j.index) ⊆ range (A.atlas.chart i.index)
  le_refl _ := Subset.rfl
  le_trans _ _ _ h₁ h₂ := h₂.trans h₁

instance : Nonempty (Chart A x) := by
  obtain ⟨i, hi⟩ := A.atlas.exists_mem_range_chart x
  exact ⟨⟨i, hi⟩⟩

instance : IsDirectedOrder (Chart A x) where
  directed i j := by
    obtain ⟨k, hk, hxk⟩ := IndexedAffinoidAtlas.exists_chart_inter i.contains j.contains
    exact ⟨⟨k, hxk⟩, hk.trans inter_subset_left, hk.trans inter_subset_right⟩

/-- The unique spectrum representative of the point in a containing chart. -/
def chartPoint (i : Chart A x) : BanachSpectrum (A.atlas.algebra i.index) :=
  i.contains.choose

@[simp]
theorem chart_chartPoint (i : Chart A x) : A.atlas.chart i.index (chartPoint A x i) = x :=
  i.contains.choose_spec

/-- The complete residue field in a containing chart. -/
abbrev Component (i : Chart A x) := CompletedResidueField K (chartPoint A x i)

theorem comap_chartPoint (i j : Chart A x) (h : i ≤ j) :
    comap (A.atlas.restriction j.index i.index h).toBoundedRingHom (chartPoint A x j) =
      chartPoint A x i := by
  apply (A.atlas.isEmbedding_chart i.index).injective
  rw [A.atlas.restriction_chart, chart_chartPoint, chart_chartPoint]

/-- The canonical isometric transition from a larger chart to a smaller chart. -/
def transition (i j : Chart A x) (h : i ≤ j) : Component A x i →ₐ[K] Component A x j :=
  (completedResidueComapOfEq K (A.atlas.restriction j.index i.index h)
    (chartPoint A x i) (chartPoint A x j) (comap_chartPoint A x i j h)).toAlgHom

theorem isometry_transition (i j : Chart A x) (h : i ≤ j) :
    Isometry (transition A x i j h) :=
  isometry_completedResidueComapOfEq K _ _ _ _

instance : DirectedSystem (Component A x) (transition A x · · ·) where
  map_self {i} z := by
    have hc : completedResidueComapOfEq K (A.atlas.restriction i.index i.index le_rfl)
        (chartPoint A x i) (chartPoint A x i) (comap_chartPoint A x i i le_rfl) =
        BoundedAlgHom.id K (Component A x i) := by
      apply completedResidueBoundedAlgHom_ext K (chartPoint A x i)
      intro a
      rw [completedResidueComapOfEq_map, A.atlas.restriction_id]
      rfl
    exact congrArg (fun f : BoundedAlgHom K (Component A x i) (Component A x i) => f z) hc
  map_map {k j i} hij hjk z := by
    have hc : (completedResidueComapOfEq K (A.atlas.restriction k.index j.index hjk)
        (chartPoint A x j) (chartPoint A x k) (comap_chartPoint A x j k hjk)).comp
        (completedResidueComapOfEq K (A.atlas.restriction j.index i.index hij)
          (chartPoint A x i) (chartPoint A x j) (comap_chartPoint A x i j hij)) =
        completedResidueComapOfEq K (A.atlas.restriction k.index i.index (hij.trans hjk))
          (chartPoint A x i) (chartPoint A x k) (comap_chartPoint A x i k (hij.trans hjk)) := by
      apply completedResidueBoundedAlgHom_ext K (chartPoint A x i)
      intro a
      change completedResidueComapOfEq K (A.atlas.restriction k.index j.index hjk)
        (chartPoint A x j) (chartPoint A x k) (comap_chartPoint A x j k hjk)
        (completedResidueComapOfEq K (A.atlas.restriction j.index i.index hij)
          (chartPoint A x i) (chartPoint A x j) (comap_chartPoint A x i j hij)
          (completedResidueMap K (chartPoint A x i) a)) = _
      rw [completedResidueComapOfEq_map, completedResidueComapOfEq_map,
        completedResidueComapOfEq_map, A.atlas.restriction_comp k.index j.index i.index hjk hij]
      rfl
    exact congrArg (fun f : BoundedAlgHom K (Component A x i) (Component A x k) => f z) hc

/-- The normed direct limit of the complete residue fields over containing charts. -/
def Limit : Type (max u w) := IsometricDirectLimit.Carrier (Component A x) (transition A x)
  (isometry_transition A x)

instance : NormedField (Limit A x) :=
  inferInstanceAs (NormedField (IsometricDirectLimit.Carrier (Component A x) (transition A x)
    (isometry_transition A x)))

instance : NormedAlgebra K (Limit A x) :=
  inferInstanceAs (NormedAlgebra K (IsometricDirectLimit.Carrier (Component A x) (transition A x)
    (isometry_transition A x)))

instance : IsUltrametricDist (Limit A x) :=
  inferInstanceAs (IsUltrametricDist (IsometricDirectLimit.Carrier (Component A x) (transition A x)
    (isometry_transition A x)))

/-- A complete ultrametric field realizing the point in every containing chart. -/
def Carrier : Type (max u w) := UniformSpace.Completion (Limit A x)

instance : NormedField (Carrier A x) :=
  inferInstanceAs (NormedField (UniformSpace.Completion (Limit A x)))

instance : CompleteSpace (Carrier A x) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (Limit A x)))

instance : NormedAlgebra K (Carrier A x) :=
  inferInstanceAs (NormedAlgebra K (UniformSpace.Completion (Limit A x)))

instance : IsUltrametricDist (Carrier A x) := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
  intro a b
  induction a, b using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih a b =>
    change ‖((a : UniformSpace.Completion (Limit A x)) + b)‖ ≤
      max ‖(a : UniformSpace.Completion (Limit A x))‖ ‖(b : UniformSpace.Completion (Limit A x))‖
    simpa only [← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe] using
      IsUltrametricDist.norm_add_le_max a b

/-- The inclusion of the normed direct limit into its completion. -/
def toCompletion : Limit A x →ₐ[K] Carrier A x where
  toRingHom := UniformSpace.Completion.coeRingHom
  commutes' _ := rfl

/-- The embedding of the residue field of a containing chart. -/
def of (i : Chart A x) : Component A x i →ₐ[K] Carrier A x :=
  (toCompletion A x).comp (IsometricDirectLimit.of (Component A x) (transition A x)
    (isometry_transition A x) i)

@[simp]
theorem norm_of (i : Chart A x) (z : Component A x i) : ‖of A x i z‖ = ‖z‖ := by
  exact (UniformSpace.Completion.norm_coe _).trans
    (IsometricDirectLimit.norm_of (Component A x) (transition A x) (isometry_transition A x) i z)

theorem of_transition (i j : Chart A x) (h : i ≤ j) (z : Component A x i) :
    of A x j (transition A x i j h z) = of A x i z :=
  congrArg (toCompletion A x) (IsometricDirectLimit.of_f (Component A x) (transition A x)
    (isometry_transition A x) h z)

/-- Compatible evaluations of the point in its complete point field. -/
def fieldPoint : FieldPoint (Carrier A x) A where
  point := x
  eval i hi := (of A x ⟨i, hi⟩).comp (completedResidueMap K (chartPoint A x ⟨i, hi⟩)).toAlgHom
  isChartPoint i hi := by
    refine ⟨chartPoint A x ⟨i, hi⟩, chart_chartPoint A x ⟨i, hi⟩, fun a => ?_⟩
    exact (norm_of A x _ _).trans (norm_completedResidueMap K _ a)
  eval_restriction i j hij hi := by
    ext a
    change of A x ⟨i, hi⟩ (completedResidueMap K (chartPoint A x ⟨i, hi⟩)
        (A.atlas.restriction i j hij a)) =
      of A x ⟨j, hij hi⟩ (completedResidueMap K (chartPoint A x ⟨j, hij hi⟩) a)
    rw [← completedResidueComapOfEq_map K (A.atlas.restriction i j hij)
      (chartPoint A x ⟨j, hij hi⟩) (chartPoint A x ⟨i, hi⟩)
      (comap_chartPoint A x ⟨j, hij hi⟩ ⟨i, hi⟩ hij)]
    exact of_transition A x ⟨j, hij hi⟩ ⟨i, hi⟩ hij _

@[simp]
theorem fieldPoint_point : (fieldPoint A x).point = x := rfl

end Langlands.Analytic.AffinoidAtlasPresentation.PointField
