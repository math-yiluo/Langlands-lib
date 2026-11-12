import Langlands.AlgebraicGeometry.PointManifold.Analytic.UnramifiedDifferential
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! # Analytic local isomorphisms for unramified affine maps in equal dimensions -/
noncomputable section
universe u
open CategoryTheory Set Filter Topology
open _root_.AlgebraicGeometry
open scoped ContDiff Manifold
namespace Langlands.AlgebraicGeometry.PointManifold.Analytic
open PointTopology
variable {k : Type u} [NontriviallyNormedField k] [CompleteSpace k]
variable {X Y : Over (Spec (CommRingCat.of k))} [IsAffine X.left] [IsAffine Y.left]
variable {d : ℕ}

namespace RegularChart

/-- The differential of a formally unramified equal-dimensional map is an isomorphism. -/
def coordinateDerivativeEquiv (c : RegularChart k X d) (c' : RegularChart k Y d)
    (f : X ⟶ Y) [FormallyUnramified f.left]
    {y : Fin d → k} (hy : y ∈ c.homeomorph.target)
    (hy' : c.homeomorph.symm y ≫ f ∈ c'.homeomorph.source) :
    (Fin d → k) ≃L[k] (Fin d → k) :=
  (LinearEquiv.ofBijective (fderiv k (c.coordinateMap c' f) y).toLinearMap
    ⟨c.coordinateMap_fderiv_injective c' f hy hy',
      (LinearMap.injective_iff_surjective).mp
        (c.coordinateMap_fderiv_injective c' f hy hy')⟩).toContinuousLinearEquiv

@[simp] theorem coordinateDerivativeEquiv_coe
    (c : RegularChart k X d) (c' : RegularChart k Y d)
    (f : X ⟶ Y) [FormallyUnramified f.left]
    {y : Fin d → k} (hy : y ∈ c.homeomorph.target)
    (hy' : c.homeomorph.symm y ≫ f ∈ c'.homeomorph.source) :
    (c.coordinateDerivativeEquiv c' f hy hy' : (Fin d → k) →L[k] (Fin d → k)) =
      fderiv k (c.coordinateMap c' f) y := rfl

/-- An analytic coordinate inverse, restricted to the overlap of the two regular charts. -/
def coordinateDiffeomorphData
    (c : RegularChart k X d) (c' : RegularChart k Y d)
    (f : X ⟶ Y) [FormallyUnramified f.left]
    {y : Fin d → k} (hy : y ∈ c.homeomorph.target)
    (hy' : c.homeomorph.symm y ≫ f ∈ c'.homeomorph.source) :
    {Φ : PartialDiffeomorph 𝓘(k, Fin d → k) 𝓘(k, Fin d → k)
        (Fin d → k) (Fin d → k) ω //
      y ∈ Φ.source ∧ (∀ z, Φ z = c.coordinateMap c' f z) ∧
      Φ.source ⊆ c.homeomorph.target ∩
        (fun z => (c.homeomorph.symm z ≫ f : RingPoint k Y k)) ⁻¹' c'.homeomorph.source} := by
  let F := c.coordinateMap c' f
  have hF := c.contDiffAt_coordinateMap c' f hy hy'
  have hs : HasStrictFDerivAt F
      (c.coordinateDerivativeEquiv c' f hy hy' : (Fin d → k) →L[k] (Fin d → k)) y :=
    hF.analyticAt.hasStrictFDerivAt
  let E := hs.toOpenPartialHomeomorph F
  let U := c.homeomorph.target ∩
    (fun z => (c.homeomorph.symm z ≫ f : RingPoint k Y k)) ⁻¹' c'.homeomorph.source
  let e := E.restr U
  have hU : U ∈ 𝓝 y := by
    refine inter_mem (c.homeomorph.open_target.mem_nhds hy) ?_
    exact ((continuous_affineSchemePointMap k k f).continuousAt.comp
      (c.homeomorph.continuousAt_symm hy)).preimage_mem_nhds
        (c'.homeomorph.open_source.mem_nhds hy')
  have heU : e.source ⊆ U := fun z hz => interior_subset hz.2
  have heF : (e : (Fin d → k) → (Fin d → k)) = F := rfl
  let Φ : PartialDiffeomorph 𝓘(k, Fin d → k) 𝓘(k, Fin d → k)
      (Fin d → k) (Fin d → k) ω := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := by
      apply contMDiffOn_iff_contDiffOn.mpr
      intro z hz
      exact (c.contDiffAt_coordinateMap c' f (heU hz).1 (heU hz).2).contDiffWithinAt
    contMDiffOn_invFun := by
      apply contMDiffOn_iff_contDiffOn.mpr
      intro z hz
      have hx := e.map_target hz
      have hcoord := c.contDiffAt_coordinateMap c' f (heU hx).1 (heU hx).2
      have hD : HasFDerivAt e
          (c.coordinateDerivativeEquiv c' f (heU hx).1 (heU hx).2 :
            (Fin d → k) →L[k] (Fin d → k)) (e.symm z) :=
        hcoord.differentiableAt (by simp) |>.hasFDerivAt
      exact (e.contDiffAt_symm hz hD hcoord).contDiffWithinAt }
  refine ⟨Φ, ?_, (fun _ => rfl), heU⟩
  exact ⟨hs.mem_toOpenPartialHomeomorph_source, mem_interior_iff_mem_nhds.mpr hU⟩

end RegularChart

namespace RegularAtlas

/-- A selected atlas chart is a partial analytic diffeomorphism. -/
def chartPartialDiffeomorph (A : RegularAtlas k X d) (p : RingPoint k X k) :
    letI := A.chartedSpace
    PartialDiffeomorph 𝓘(k, Fin d → k) 𝓘(k, Fin d → k)
      (RingPoint k X k) (Fin d → k) ω := by
  letI := A.chartedSpace
  letI := A.isManifold
  exact {
    toPartialEquiv := (A.chartAt p).homeomorph.toPartialEquiv
    open_source := (A.chartAt p).homeomorph.open_source
    open_target := (A.chartAt p).homeomorph.open_target
    contMDiffOn_toFun := contMDiffOn_chart (I := 𝓘(k, Fin d → k))
    contMDiffOn_invFun := contMDiffOn_chart_symm (I := 𝓘(k, Fin d → k)) }

/-- Every formally unramified morphism between equal-dimensional regular atlases
induces an analytic local diffeomorphism on actual points. -/
theorem isLocalDiffeomorph_postcomp
    (A : RegularAtlas k X d) (B : RegularAtlas k Y d)
    (f : X ⟶ Y) [FormallyUnramified f.left] :
    letI := A.chartedSpace
    letI := B.chartedSpace
    IsLocalDiffeomorph (M := RingPoint k X k) (N := RingPoint k Y k)
      𝓘(k, Fin d → k) 𝓘(k, Fin d → k) ω
      (fun p : RingPoint k X k => (p ≫ f : RingPoint k Y k)) := by
  letI := A.chartedSpace
  letI := B.chartedSpace
  intro p
  let c := A.chartAt p
  let c' := B.chartAt (p ≫ f)
  have hp : p ∈ c.homeomorph.source := A.mem_source p
  have hy : c.homeomorph p ∈ c.homeomorph.target := c.homeomorph.map_source hp
  have hy' : c.homeomorph.symm (c.homeomorph p) ≫ f ∈ c'.homeomorph.source := by
    rw [c.homeomorph.left_inv hp]
    exact B.mem_source (p ≫ f)
  let D := c.coordinateDiffeomorphData c' f hy hy'
  let Φ := ((A.chartPartialDiffeomorph p).trans D.val).trans
    (B.chartPartialDiffeomorph (p ≫ f)).symm
  refine ⟨Φ, ?_, ?_⟩
  · refine ⟨⟨hp, D.property.1⟩, ?_⟩
    change D.val (c.homeomorph p) ∈ c'.homeomorph.target
    rw [D.property.2.1]
    change c'.homeomorph (c.homeomorph.symm (c.homeomorph p) ≫ f) ∈ _
    exact c'.homeomorph.map_source hy'
  · intro q hq
    have hsource : c.homeomorph q ∈ D.val.source := hq.1.2
    have htarget := (D.property.2.2 hsource).2
    change q ≫ f = c'.homeomorph.symm (D.val (c.homeomorph q))
    rw [D.property.2.1, RegularChart.coordinateMap, c'.homeomorph.left_inv htarget]
    exact congrArg (fun r : RingPoint k X k => (r ≫ f : RingPoint k Y k))
      (c.homeomorph.left_inv hq.1.1).symm

end RegularAtlas

/-- Etale affine scheme morphisms give analytic local diffeomorphisms for the
manifolds constructed from algebraic smoothness. -/
theorem smoothAffine_isLocalDiffeomorph_etale
    (hX : SmoothOfRelativeDimension d X.hom) (hY : SmoothOfRelativeDimension d Y.hom)
    (f : X ⟶ Y) [Etale f.left] :
    letI := smoothAffineChartedSpace k X d hX
    letI := smoothAffineChartedSpace k Y d hY
    IsLocalDiffeomorph (M := RingPoint k X k) (N := RingPoint k Y k)
      𝓘(k, Fin d → k) 𝓘(k, Fin d → k) ω
      (fun p : RingPoint k X k => (p ≫ f : RingPoint k Y k)) :=
  (smoothAffineRegularAtlas k X d hX).isLocalDiffeomorph_postcomp
    (smoothAffineRegularAtlas k Y d hY) f

end Langlands.AlgebraicGeometry.PointManifold.Analytic
