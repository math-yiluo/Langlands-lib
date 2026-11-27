import Langlands.Geometry.Analytic.AffineAnalytificationSeminormProof
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! # Joint evaluation of finite sums on affine analytifications -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.AffineAnalytification

open Topology Filter

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)

variable {T : Type z} [TopologicalSpace T] {ι : Type w} (I : Finset ι)
  (a : ι → A) (c : ι → T → K)

local notation "L" => Space K P

/-- Evaluate a finite linear combination of fixed algebra elements with continuously
varying scalar coefficients. The evaluation is continuous jointly in the coefficient
parameter and the affine analytic point. -/
theorem continuous_pointSeminorm_sum (hc : ∀ i ∈ I, Continuous (c i)) :
    Continuous (fun p : T × L =>
      pointSeminorm K P p.2 (∑ i ∈ I, algebraMap K A (c i p.1) * a i)) := by
  let S := fun t : T => ∑ i ∈ I, algebraMap K A (c i t) * a i
  rw [continuous_iff_continuousAt]
  intro z
  let F := fun p : T × L => pointSeminorm K P p.2 (S p.1)
  let fixed := fun p : T × L => pointSeminorm K P p.2 (S z.1)
  let B := fun p : T × L => ∑ i ∈ I, ‖c i p.1 - c i z.1‖ * pointSeminorm K P p.2 (a i)
  have hcFixed : Continuous fixed := (continuous_pointSeminorm_apply K P (S z.1)).comp continuous_snd
  have hcB : Continuous B := by
    apply continuous_finsetSum
    intro i hi
    exact (((hc i hi).comp continuous_fst).sub continuous_const).norm.mul
      ((continuous_pointSeminorm_apply K P (a i)).comp continuous_snd)
  have hBz : B z = 0 := by simp [B]
  have hbound (p : T × L) : dist (F p) (fixed p) ≤ B p := by
    let ν := pointSeminorm K P p.2
    calc
      _ ≤ ν (S p.1 - S z.1) := by
        rw [Real.dist_eq]
        exact abs_sub_map_le_sub ν _ _
      _ = ν (∑ i ∈ I, algebraMap K A (c i p.1 - c i z.1) * a i) := by
        congr 1
        simp only [S, Finset.sum_sub_distrib, map_sub, sub_mul]
      _ ≤ ∑ i ∈ I, ν (algebraMap K A (c i p.1 - c i z.1) * a i) :=
        SeminormComparison.map_sum_le_sum ν I _
      _ = B p := by
        apply Finset.sum_congr rfl
        intro i _
        rw [map_mul]
        exact congrArg (· * ν (a i)) (pointSeminorm_extendsNorm K P p.2 (c i p.1 - c i z.1))
  change Tendsto F (𝓝 z) (𝓝 (F z))
  apply tendsto_iff_dist_tendsto_zero.2
  have hcDom : Continuous (fun p => B p + dist (fixed p) (fixed z)) :=
    hcB.add (hcFixed.dist continuous_const)
  refine squeeze_zero (g := fun p => B p + dist (fixed p) (fixed z))
    (fun _ => dist_nonneg) (fun p => ?_) ?_
  · change dist (F p) (fixed z) ≤ B p + dist (fixed p) (fixed z)
    exact (dist_triangle _ (fixed p) _).trans (add_le_add_left (hbound p) _)
  · simpa only [hBz, dist_self, add_zero] using hcDom.tendsto z

/-- The continuous evaluation map of the specified family of affine algebra elements. -/
def finiteCoefficientEvaluation (hc : ∀ i ∈ I, Continuous (c i)) : C(T × L, ℝ) :=
  ⟨fun p => pointSeminorm K P p.2 (∑ i ∈ I, algebraMap K A (c i p.1) * a i),
    continuous_pointSeminorm_sum K P I a c hc⟩

end Langlands.Analytic.AffineAnalytification
