import Langlands.AlgebraicGeometry.PointManifold.Analytic.EvaluationDerivation
import Langlands.AlgebraicGeometry.PointManifold.Analytic.SmoothAffineManifold
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMapProofs

/-! # Injectivity of differentials for unramified maps in regular analytic charts -/
noncomputable section
universe u
open CategoryTheory Set Filter Topology
open _root_.AlgebraicGeometry
open scoped ContDiff Manifold
namespace Langlands.AlgebraicGeometry.PointManifold.Analytic
open PointTopology
variable {k : Type u} [NontriviallyNormedField k] [CompleteSpace k]
variable {X Y : Over (Spec (CommRingCat.of k))} [IsAffine X.left] [IsAffine Y.left]
variable {d e : ℕ}

namespace RegularChart

/-- Inverse-chart regular evaluations are analytic at every point of the target. -/
theorem contDiffAt_inverse_evaluation (c : RegularChart k X d)
    {y : Fin d → k} (hy : y ∈ c.homeomorph.target) (a : AffineCoordinateRing k X) :
    ContDiffAt k ω (fun z => regularEvaluation (c.homeomorph.symm z) a) y :=
  (c.contDiffOn_inverse_evaluation a).contDiffAt (c.homeomorph.open_target.mem_nhds hy)

/-- A vector killing every regular evaluation in a regular chart is zero. -/
theorem tangent_eq_zero (c : RegularChart k X d) {y v : Fin d → k}
    (hy : y ∈ c.homeomorph.target)
    (hz : ∀ a : AffineCoordinateRing k X,
      fderiv k (fun z => regularEvaluation (c.homeomorph.symm z) a) y v = 0) : v = 0 := by
  funext i
  let F : (Fin d → k) → k × k := fun z =>
    (regularEvaluation (c.homeomorph.symm z) (c.numerator i),
      regularEvaluation (c.homeomorph.symm z) (c.denominator i))
  let g : k × k → k := fun q => q.1 * q.2⁻¹
  have hF := ((c.contDiffAt_inverse_evaluation hy (c.numerator i)).differentiableAt
      (by simp)).hasFDerivAt.prodMk
    ((c.contDiffAt_inverse_evaluation hy (c.denominator i)).differentiableAt
      (by simp)).hasFDerivAt
  have hg : DifferentiableAt k g (F y) :=
    (contDiffAt_fst.mul (contDiffAt_snd.inv
      (c.denominator_ne_zero _ (c.homeomorph.map_target hy) i))).differentiableAt
        (show (ω : WithTop ℕ∞) ≠ 0 by simp)
  have hcomp := hg.hasFDerivAt.comp y hF
  have heq : g ∘ F =ᶠ[𝓝 y] (fun z : Fin d → k => z i) := by
    filter_upwards [c.homeomorph.open_target.mem_nhds hy] with z hz'
    have h := c.apply_eq (c.homeomorph.symm z) (c.homeomorph.map_target hz') i
    rw [c.homeomorph.right_inv hz'] at h
    simpa only [Function.comp_apply, g, F, div_eq_mul_inv] using h.symm
  have hd : fderiv k (g ∘ F) y = ContinuousLinearMap.proj i :=
    heq.fderiv_eq.trans (hasFDerivAt_apply i y).fderiv
  have hval := congrArg (fun D : (Fin d → k) →L[k] k => D v) hcomp.fderiv
  rw [hd] at hval
  change v i = _ at hval
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    hz, Prod.mk_zero_zero, map_zero, Pi.zero_apply] using hval

/-- The point map in two regular analytic coordinate systems. -/
def coordinateMap (c : RegularChart k X d) (c' : RegularChart k Y e) (f : X ⟶ Y) :
    (Fin d → k) → (Fin e → k) :=
  fun z => c'.homeomorph (c.homeomorph.symm z ≫ f)

/-- The coordinate map of an actual affine morphism is analytic on the overlapping charts. -/
theorem contDiffAt_coordinateMap (c : RegularChart k X d) (c' : RegularChart k Y e)
    (f : X ⟶ Y) {y : Fin d → k} (hy : y ∈ c.homeomorph.target)
    (hy' : c.homeomorph.symm y ≫ f ∈ c'.homeomorph.source) :
    ContDiffAt k ω (c.coordinateMap c' f) y := by
  have hc : ContinuousAt (X := Fin d → k) (Y := RingPoint k Y k) (fun z => (c.homeomorph.symm z ≫ f : RingPoint k Y k)) y :=
    (continuous_affineSchemePointMap k k f).continuousAt.comp (c.homeomorph.continuousAt_symm hy)
  have hnear := hc.preimage_mem_nhds (c'.homeomorph.open_source.mem_nhds hy')
  refine contDiffAt_pi.2 fun i => ?_
  have hn := c.contDiffAt_inverse_evaluation hy (affineCoordinatePullback k f (c'.numerator i))
  have hd := c.contDiffAt_inverse_evaluation hy (affineCoordinatePullback k f (c'.denominator i))
  have hden : regularEvaluation (c.homeomorph.symm y)
      (affineCoordinatePullback k f (c'.denominator i)) ≠ 0 := by
    rw [← regularEvaluation_postcomp]
    exact c'.denominator_ne_zero _ hy' i
  refine (hn.mul (hd.inv hden)).congr_of_eventuallyEq ?_
  filter_upwards [hnear] with z hz
  change c'.homeomorph (c.homeomorph.symm z ≫ f) i = _
  rw [c'.apply_eq _ hz i, div_eq_mul_inv, regularEvaluation_postcomp, regularEvaluation_postcomp]
  rfl

/-- Formal unramifiedness makes the analytic differential injective in regular charts. -/
theorem coordinateMap_fderiv_injective (c : RegularChart k X d) (c' : RegularChart k Y e)
    (f : X ⟶ Y) [FormallyUnramified f.left]
    {y : Fin d → k} (hy : y ∈ c.homeomorph.target)
    (hy' : c.homeomorph.symm y ≫ f ∈ c'.homeomorph.source) :
    Function.Injective (fderiv k (c.coordinateMap c' f) y) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change (fderiv k (c.coordinateMap c' f) y) v = 0 at hv
  have hF := (c.contDiffAt_coordinateMap c' f hy hy').differentiableAt (by simp)
  have htarget : c.coordinateMap c' f y ∈ c'.homeomorph.target := c'.homeomorph.map_source hy'
  have hc : ContinuousAt (X := Fin d → k) (Y := RingPoint k Y k) (fun z => (c.homeomorph.symm z ≫ f : RingPoint k Y k)) y :=
    (continuous_affineSchemePointMap k k f).continuousAt.comp (c.homeomorph.continuousAt_symm hy)
  have hnear := hc.preimage_mem_nhds (c'.homeomorph.open_source.mem_nhds hy')
  have hbase : ∀ a : AffineCoordinateRing k Y,
      fderiv k (fun z => regularEvaluation (c.homeomorph.symm z)
        (affineCoordinatePullback k f a)) y v = 0 := by
    intro a
    let g := fun z => regularEvaluation (c'.homeomorph.symm z) a
    have hg := (c'.contDiffAt_inverse_evaluation htarget a).differentiableAt (by simp)
    have heq : (fun z => regularEvaluation (c.homeomorph.symm z)
        (affineCoordinatePullback k f a)) =ᶠ[𝓝 y] g ∘ c.coordinateMap c' f := by
      filter_upwards [hnear] with z hz
      dsimp only [Function.comp_apply, coordinateMap, g]
      rw [c'.homeomorph.left_inv hz, regularEvaluation_postcomp]
    rw [heq.fderiv_eq, fderiv_comp y hg hF, ContinuousLinearMap.comp_apply, hv, map_zero]
  apply c.tangent_eq_zero hy
  exact evaluationDerivation_eq_zero_of_unramified (affineCoordinatePullback k f)
    (fun z => regularEvaluation (c.homeomorph.symm z)) y v
    (fun a => (c.contDiffAt_inverse_evaluation hy a).differentiableAt (by simp))
    ((HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified) (f := f.left)).mp
      inferInstance) hbase

end RegularChart
end Langlands.AlgebraicGeometry.PointManifold.Analytic
