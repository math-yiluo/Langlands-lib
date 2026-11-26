import Langlands.HarmonicAnalysis.UltrametricBallPushforward
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! # Centered Haar charts from a strict derivative -/

noncomputable section

namespace Langlands.Analysis

open Filter MeasureTheory Metric Set _root_.Topology
open scoped NNReal

universe u v w

variable {F : Type u} [NontriviallyNormedField F]
  {X : Type v} [NormedAddCommGroup X] [NormedSpace F X] [IsUltrametricDist X] [ProperSpace X]
  {Y : Type w} [NormedAddCommGroup Y] [NormedSpace F Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

/-- At the origin, a strict derivative that is a linear equivalence gives
centered open ball charts and identifies their additive Haar pushforwards. -/
theorem exists_strictDerivative_ballChart (μ : Measure X) [μ.IsAddHaarMeasure]
    (f : X → Y) (e : X ≃L[F] Y) (hf : HasStrictFDerivAt f (e : X →L[F] Y) 0)
    (h₀ : f 0 = 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r ≤ R →
      let B := closedBall (0 : X) r
      IsOpenEmbedding (fun x : B => f x.val) ∧ f '' B = e '' B ∧
        (μ.restrict B).map f = (μ.map e).restrict (e '' B) := by
  classical
  let g : X → X := fun x => e.symm (f x)
  have hzero : g 0 = 0 := by simp [g, h₀]
  have hder : HasStrictFDerivAt g (ContinuousLinearMap.id F X) 0 := by
    have hh := (e.symm : Y →L[F] X).hasStrictFDerivAt.comp 0 hf
    change HasStrictFDerivAt g ((e.symm : Y →L[F] X).comp (e : X →L[F] Y)) 0 at hh
    convert hh using 1
    ext x
    exact (e.symm_apply_apply x).symm
  let u : X → X := fun x => g x - x
  let c : ℝ≥0 := 1 / 2
  have hc₀ : 0 < c := by norm_num [c]
  have hc : c < 1 := by norm_num [c]
  obtain ⟨s, hs, ha⟩ := hder.approximates_deriv_on_nhds (Or.inr hc₀)
  have hLip : LipschitzOnWith c u s := ha.lipschitzOnWith
  obtain ⟨R₀, hR₀, hRs⟩ := Metric.mem_nhds_iff.mp hs
  let R := R₀ / 2
  have hR : 0 < R := half_pos hR₀
  refine ⟨R, hR, fun r hr hrR => ?_⟩
  let B := closedBall (0 : X) r
  have hBs : B ⊆ s := (closedBall_subset_ball (hrR.trans_lt (half_lt_self hR₀))).trans hRs
  have hBcl : IsClopen B := ⟨isClosed_closedBall, IsUltrametricDist.isOpen_closedBall _ hr.ne'⟩
  have hB₀ : (0 : X) ∈ B := mem_closedBall_self hr.le
  let v : X → X := B.piecewise u 0
  have hv (x : X) (hx : x ∈ B) : v x = u x := Set.piecewise_eq_of_mem _ _ _ hx
  have hu₀ : u 0 = 0 := by simp [u, hzero]
  have hv₀ : v 0 = 0 := (hv 0 hB₀).trans hu₀
  have hLv : LipschitzOnWith c v B := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [hv x hx, hv y hy]
    exact hLip.dist_le_mul x (hBs hx) y (hBs hy)
  have hcv : Continuous v := by
    apply continuous_piecewise
    · simp [hBcl.frontier_eq]
    · rw [hBcl.isClosed.closure_eq]
      exact (hLip.mono hBs).continuousOn
    · exact continuous_zero.continuousOn
  let F' : X → X := fun x => x + v x
  have hF' : Continuous F' := continuous_id.add hcv
  have hF'val (x : X) (hx : x ∈ B) : F' x = g x := by
    change x + v x = g x
    rw [hv x hx]
    dsimp only [u]
    abel
  have hbound (x : X) (hx : x ∈ B) : ‖v x‖ ≤ r := by
    have hb := hLv.dist_le_mul x hx 0 hB₀
    rw [hv₀, dist_zero_right, dist_zero_right] at hb
    exact hb.trans ((mul_le_of_le_one_left (norm_nonneg _) (by exact_mod_cast hc.le)).trans
      (mem_closedBall_zero_iff.mp hx))
  have hIm : F' '' B = B := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact mem_closedBall_zero_iff.mpr ((IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le (mem_closedBall_zero_iff.mp hx) (hbound x hx)))
    · intro b hb
      let j : X → X := fun x => b - v x
      have hLj : LipschitzOnWith c j B := by
        apply LipschitzOnWith.of_dist_le_mul
        intro x hx y hy
        change dist (b - v x) (b - v y) ≤ _
        rw [dist_eq_norm, show b - v x - (b - v y) = -(v x - v y) by abel,
          norm_neg, ← dist_eq_norm]
        exact hLv.dist_le_mul x hx y hy
      have hBj : MapsTo j B B := by
        intro x hx
        apply mem_closedBall_zero_iff.mpr
        change ‖b - v x‖ ≤ r
        rw [sub_eq_add_neg]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le (mem_closedBall_zero_iff.mp hb) (by rw [norm_neg]; exact hbound x hx))
      obtain ⟨x, hx, he, _, _⟩ := ContractingWith.exists_fixedPoint' (K := c) (f := j)
        isClosed_closedBall.isComplete hBj ⟨hc, hLj.to_restrict⟩ hB₀ (edist_ne_top _ _)
      change b - v x = x at he
      exact ⟨x, hx, (sub_eq_iff_eq_add.mp he).symm⟩
  have hF'inj : InjOn F' B := by
    intro x hx y hy hxy
    have hEq : x - y = -(v x - v y) := by
      change x + v x = y + v y at hxy
      rw [eq_neg_iff_add_eq_zero, ← add_sub_add_comm, hxy, sub_self]
    have hL := hLv.dist_le_mul x hx y hy
    rw [dist_eq_norm, dist_eq_norm, hEq, norm_neg] at hL
    by_contra! hne
    have hz : 0 < ‖v x - v y‖ := by
      rw [← norm_neg, ← hEq]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    exact (not_lt_of_ge hL) (mul_lt_of_lt_one_left hz (by exact_mod_cast hc))
  have hfEq (x : X) (hx : x ∈ B) : f x = e (F' x) := by
    rw [hF'val x hx]
    exact (e.apply_symm_apply _).symm
  have hI : f '' B = e '' B := by
    calc
      f '' B = (e ∘ F') '' B := Set.image_congr hfEq
      _ = e '' (F' '' B) := by simp only [Set.image_image, Function.comp_def]
      _ = e '' B := by rw [hIm]
  have hcont : Continuous (fun x : B => f x.val) :=
    ((e.continuous.comp hF').comp continuous_subtype_val).congr fun x => (hfEq x.val x.property).symm
  have hi : Function.Injective (fun x : B => f x.val) := by
    intro x y he
    apply Subtype.ext
    change f x.val = f y.val at he
    rw [hfEq _ x.property, hfEq _ y.property] at he
    exact hF'inj x.property y.property (e.injective he)
  let : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 r)
  have hOpenRange : IsOpen (range (fun x : B => f x.val)) := by
    rw [show range (fun x : B => f x.val) = f '' B from Set.range_domRestrict _ _,
      hI]
    exact e.toHomeomorph.isOpenMap B hBcl.isOpen
  refine ⟨⟨(hcont.isClosedEmbedding hi).isEmbedding, hOpenRange⟩, hI, ?_⟩
  have hmap : (μ.restrict B).map F' = μ.restrict B := by
    simpa only [F', hv₀, add_zero] using
      Langlands.HarmonicAnalysis.map_closedBall_add_perturbation μ 0 hr.le hLv hc hcv
  have hAE : f =ᵐ[μ.restrict B] e ∘ F' :=
    (ae_restrict_mem hBcl.isClosed.measurableSet).mono fun x hx => hfEq x hx
  rw [Measure.map_congr hAE, ← Measure.map_map e.continuous.measurable hF'.measurable, hmap]
  have hh := e.toHomeomorph.measurableEmbedding.restrict_map μ (e '' B)
  change (μ.map e).restrict (e '' B) = (μ.restrict (e ⁻¹' (e '' B))).map e at hh
  rw [Set.preimage_image_eq _ e.injective] at hh
  exact hh.symm

end Langlands.Analysis
