import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceAnalyticStructure

/-! # Local calculus for varying-dimension point atlases -/

noncomputable section

universe u

open CategoryTheory Set Filter Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped ContDiff Manifold

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.DimensionPointAtlas

variable {K : Type u} [NontriviallyNormedField K]
  {X Y Z : AlgebraicSpace (Spec (CommRingCat.of K))}
  {hX : SmoothOverBase X} {hY : SmoothOverBase Y} {hZ : SmoothOverBase Z}
  (A : DimensionPointAtlas hX) (B : DimensionPointAtlas hY) (C : DimensionPointAtlas hZ)

/-- Pointwise analyticity, tested in every pair of charts containing the point
and its image. -/
def AnalyticAt (f : RingPoints K X K → RingPoints K Y K)
    (x : RingPoints K X K) : Prop :=
  letI := etaleChartTopology K X
  letI := etaleChartTopology K Y
  ContinuousAt f x ∧ ∀ n m, ∀ e ∈ A.atlas n, ∀ e' ∈ B.atlas m,
    x ∈ e.source → f x ∈ e'.source →
      ContDiffAt K ω (e' ∘ f ∘ e.symm) (e x)

variable {A B C}

/-- On an open set, the all-chart definition gives pointwise analyticity. -/
theorem AnalyticOn.analyticAt {f : RingPoints K X K → RingPoints K Y K}
    {s : Set (RingPoints K X K)} (hf : A.AnalyticOn B f s)
    (hs : @IsOpen _ (etaleChartTopology K X) s) {x : RingPoints K X K}
    (hx : x ∈ s) : A.AnalyticAt B f x := by
  let := etaleChartTopology K X
  let := etaleChartTopology K Y
  have hfc : ContinuousAt f x := hf.1.continuousAt (hs.mem_nhds hx)
  refine ⟨hfc, ?_⟩
  intro n m e he e' he' hxe hfe
  apply (hf.2 n m e he e' he').contDiffAt
  apply inter_mem (e.open_target.mem_nhds (e.map_source hxe))
  apply e.tendsto_symm hxe
  exact inter_mem (hs.mem_nhds hx) (hfc (e'.open_source.mem_nhds hfe))

/-- A global analytic map is analytic at every point. -/
theorem AnalyticMap.analyticAt {f : RingPoints K X K → RingPoints K Y K}
    (hf : A.AnalyticMap B f) (x : RingPoints K X K) : A.AnalyticAt B f x := by
  let := etaleChartTopology K X
  exact AnalyticOn.analyticAt hf isOpen_univ (mem_univ x)

/-- Pointwise analyticity on the original points yields the full all-chart map. -/
theorem analyticMap_of_analyticAt {f : RingPoints K X K → RingPoints K Y K}
    (hf : ∀ x, A.AnalyticAt B f x) : A.AnalyticMap B f := by
  let := etaleChartTopology K X
  let := etaleChartTopology K Y
  refine ⟨(continuous_iff_continuousAt.mpr fun x => (hf x).1).continuousOn, ?_⟩
  intro n m e he e' he' y hy
  have h := (hf (e.symm y)).2 n m e he e' he' (e.map_target hy.1) hy.2.2
  rw [e.right_inv hy.1] at h
  exact h.contDiffWithinAt

/-- Pointwise analyticity depends only on the germ of the map. -/
theorem AnalyticAt.congr_of_eventuallyEq
    {f g : RingPoints K X K → RingPoints K Y K} {x : RingPoints K X K}
    (hf : A.AnalyticAt B f x)
    (hgf : @Filter.EventuallyEq _ _ (@nhds _ (etaleChartTopology K X) x) g f) :
    A.AnalyticAt B g x := by
  let := etaleChartTopology K X
  let := etaleChartTopology K Y
  have hval : g x = f x := hgf.eq_of_nhds
  refine ⟨hf.1.congr_of_eventuallyEq hgf, ?_⟩
  intro n m e he e' he' hx hgx
  have h := hf.2 n m e he e' he' hx (hval ▸ hgx)
  apply h.congr_of_eventuallyEq
  filter_upwards [(e.tendsto_symm hx).eventually hgf] with y hy
  exact congrArg e' hy

/-- Pointwise analytic maps compose even when dimensions vary. -/
theorem AnalyticAt.comp
    {f : RingPoints K X K → RingPoints K Y K}
    {g : RingPoints K Y K → RingPoints K Z K} {x : RingPoints K X K}
    (hg : B.AnalyticAt C g (f x)) (hf : A.AnalyticAt B f x) :
    A.AnalyticAt C (g ∘ f) x := by
  let := etaleChartTopology K X
  let := etaleChartTopology K Y
  let := etaleChartTopology K Z
  refine ⟨hg.1.comp hf.1, ?_⟩
  intro n p e he e' he' hx hgx
  let b := B.chartAt (f x)
  have hb := B.chart_mem_atlas (f x)
  have hbx := B.mem_chart_source (f x)
  have hfc := hf.2 n _ e he b hb hx hbx
  have hgc := hg.2 _ p b hb e' he' hbx hgx
  have hgc' : ContDiffAt K ω (e' ∘ g ∘ b.symm)
      ((b ∘ f ∘ e.symm) (e x)) := by
    simpa only [Function.comp_apply, e.left_inv hx] using hgc
  have hcomp := hgc'.comp (e x) hfc
  apply hcomp.congr_of_eventuallyEq
  have hmem : ∀ᶠ y in 𝓝 (e x), f (e.symm y) ∈ b.source :=
    (hf.1.tendsto.comp (e.tendsto_symm hx)).eventually (b.open_source.mem_nhds hbx)
  filter_upwards [hmem] with y hy
  change e' (g (f (e.symm y))) = e' (g (b.symm (b (f (e.symm y)))))
  rw [b.left_inv hy]

/-- Analytic coordinate maps into and out of a model space compose. -/
theorem analyticMap_comp_model {m : ℕ}
    {c : RingPoints K X K → (Fin m → K)} {d : (Fin m → K) → RingPoints K Y K}
    (hc : A.AnalyticToModel c) (hd : B.AnalyticFromModel d) :
    A.AnalyticMap B (d ∘ c) := by
  let := etaleChartTopology K X
  let := etaleChartTopology K Y
  apply analyticMap_of_analyticAt
  intro x
  refine ⟨hd.1.continuousAt.comp hc.1.continuousAt, ?_⟩
  intro n p e he e' he' hx hdx
  have hcc := (hc.2 n e he).contDiffAt (e.open_target.mem_nhds (e.map_source hx))
  have hdc := (hd.2 p e' he').contDiffAt
    (hd.1.continuousAt (e'.open_source.mem_nhds hdx))
  have hdc' : ContDiffAt K ω (e' ∘ d) ((c ∘ e.symm) (e x)) := by
    simpa only [Function.comp_apply, e.left_inv hx] using hdc
  exact hdc'.comp (e x) hcc

end Langlands.AlgebraicGeometry.AlgebraicSpace.DimensionPointAtlas
