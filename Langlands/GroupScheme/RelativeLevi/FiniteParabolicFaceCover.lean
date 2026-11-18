import Langlands.GroupScheme.RelativeLevi.AffineParabolicFaceChart
import Langlands.GroupScheme.RelativeUnipotent.RootWeightSeries
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # A finite affine etale face-chart cover with one termination bound -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {G H : GroupScheme S} [IsAffineHom G.X.hom]
  {p : H ⟶ G}

local instance {T : Scheme.{u}} (b : T ⟶ S) :
    IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

namespace AffineParabolicFaceChart

variable {s : S} (C : AffineParabolicFaceChart p s)

/-- The finite maximum of the chart's original unscaled face weights. -/
def maxWeight : ℕ :=
  letI := C.coordinateFintype
  letI := C.rootFintype
  C.chart.weights.weightBound

end AffineParabolicFaceChart

/-- Finitely many actual face charts covering the original base, together
with one bound for all their unchanged canonical face weights. -/
structure FiniteParabolicFaceCover (p : H ⟶ G) where
  count : ℕ
  charts : Fin count → Σ s : S, AffineParabolicFaceChart p s
  covers : ∀ s : S, ∃ a : Fin count,
    s ∈ Set.range (charts a).2.projection
  bound : ℕ
  bound_ge : ∀ a : Fin count, (charts a).2.maxWeight ≤ bound

namespace FiniteParabolicFaceCover

variable (D : FiniteParabolicFaceCover p)

/-- The finite coproduct of the actual affine chart schemes. -/
def space : Scheme.{u} := ∐ (fun a : Fin D.count => Spec (D.charts a).2.ring)

/-- The actual jointly surjective map from the finite coproduct to the original base. -/
def baseMap : D.space ⟶ S := Sigma.desc (fun a : Fin D.count => (D.charts a).2.projection)

instance isAffine_space : IsAffine D.space := by
  dsimp [space]
  infer_instance

instance etale_baseMap : Etale D.baseMap := by
  apply IsZariskiLocalAtSource.sigmaDesc (P := @Etale)
  intro a
  exact (D.charts a).2.etale

instance surjective_baseMap : Surjective D.baseMap := by
  constructor
  intro s
  obtain ⟨a, y, hy⟩ := D.covers s
  let X := fun a : Fin D.count => Spec (D.charts a).2.ring
  refine ⟨Sigma.ι X a y, ?_⟩
  have he : Sigma.ι X a ≫ D.baseMap = (D.charts a).2.projection := Sigma.ι_comp_desc _ _
  have hv := congrArg (fun f => f y) he
  rw [Scheme.Hom.comp_apply] at hv
  exact hv.trans hy

/-- Every original local face weight is at most the one common bound. -/
theorem weight_le_bound (a : Fin D.count) :
    letI := (D.charts a).2.coordinateFintype
    letI := (D.charts a).2.rootFintype
    ∀ k, (D.charts a).2.chart.weights.weight k ≤ D.bound := by
  letI := (D.charts a).2.coordinateFintype
  letI := (D.charts a).2.rootFintype
  intro k
  exact ((D.charts a).2.chart.weights.weight_le_weightBound k).trans (D.bound_ge a)

end FiniteParabolicFaceCover

variable (p : H ⟶ G) (hG : IsReductive G) (hp : IsRelativeParabolicSubgroup p)

include hG hp in
/-- Compactness extracts a finite collection of actual affine etale face
charts and a common finite bound from the derived pointwise charts. -/
theorem nonempty_finiteParabolicFaceCover [CompactSpace S] :
    Nonempty (FiniteParabolicFaceCover p) := by
  classical
  let C (s : S) := affineParabolicFaceChartAt p hG hp s
  have hopen (s : S) : IsOpen (Set.range (C s).projection) := by
    letI := (C s).etale
    exact (C s).projection.isOpenMap.isOpen_range
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover
    (fun s : S => Set.range (C s).projection)
    (fun s => (hopen s).mem_nhds ⟨(C s).point, (C s).point_over⟩)
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  let charts : Fin (Fintype.card t) → Σ s : S, AffineParabolicFaceChart p s :=
    fun a => ⟨(e a).val, C (e a).val⟩
  have hcover (s : S) : ∃ a : Fin (Fintype.card t), s ∈ Set.range (charts a).2.projection := by
    have hs : s ∈ (⊤ : Set S) := trivial
    rw [← ht, Set.mem_iUnion] at hs
    rcases hs with ⟨y, _, ⟨hy, rfl⟩, hs⟩
    obtain ⟨a, ha⟩ := e.surjective ⟨y, hy⟩
    refine ⟨a, ?_⟩
    change s ∈ Set.range (C (e a).val).projection
    rw [ha]
    exact hs
  let n := Finset.univ.sup (fun a : Fin (Fintype.card t) => (charts a).2.maxWeight)
  exact ⟨⟨Fintype.card t, charts, hcover, n, fun a => Finset.le_sup (f := fun a : Fin (Fintype.card t) => (charts a).2.maxWeight)
    (Finset.mem_univ a)⟩⟩

/-- Choose the constructed finite face-chart cover and its common termination bound. -/
def finiteParabolicFaceCover [CompactSpace S] : FiniteParabolicFaceCover p :=
  Classical.choice (nonempty_finiteParabolicFaceCover p hG hp)

end Langlands.GroupScheme.RelativeLevi
