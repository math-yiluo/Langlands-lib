import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof

/-! # Local change of variables for an invertible strict derivative -/

open Filter MeasureTheory MeasureTheory.Measure Metric Set
open scoped NNReal Topology

namespace Langlands.Analysis

universe u v w

section Local

variable {K X Y : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup X] [NormedSpace K X] [IsUltrametricDist X]

private theorem dist_eq_of_approximatesLinearOn_id
    {f : X → X} {s : Set X} {c : ℝ≥0}
    (hf : ApproximatesLinearOn f (ContinuousLinearMap.id K X) s c) (hc : c < 1)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) : dist (f x) (f y) = dist x y := by
  by_cases hxy : x = y
  · simp [hxy]
  rw [dist_eq_norm, dist_eq_norm]
  have hlt : ‖f x - f y - (x - y)‖ < ‖x - y‖ := by
    calc
      ‖f x - f y - (x - y)‖ ≤ (c : ℝ) * ‖x - y‖ := hf x hx y hy
      _ < ‖x - y‖ := mul_lt_of_lt_one_left (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) hc
  calc
    ‖f x - f y‖ = ‖f x - f y - (x - y) + (x - y)‖ := by rw [sub_add_cancel]
    _ = ‖x - y‖ := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne, max_eq_right hlt.le]

private theorem surjOn_closedBall_of_approximatesLinearOn_id [CompleteSpace X]
    {f : X → X} {a : X} {r : ℝ} {c : ℝ≥0}
    (hf : ApproximatesLinearOn f (ContinuousLinearMap.id K X) (closedBall a r) c)
    (hc : c < 1) (hr : 0 ≤ r) : SurjOn f (closedBall a r) (closedBall (f a) r) := by
  intro z hz
  let g : X → X := fun x => z - (f x - x)
  have ha : a ∈ closedBall a r := mem_closedBall_self hr
  have hgLip : LipschitzOnWith c g (closedBall a r) := by
    apply lipschitzOnWith_iff_norm_sub_le.mpr
    intro x hx y hy
    have hdiff : g x - g y = -(f x - f y - (x - y)) := by
      dsimp [g]
      abel
    rw [hdiff, norm_neg]
    exact hf x hx y hy
  have hga : dist (g a) a = dist z (f a) := by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    dsimp [g]
    abel
  have hgMap : MapsTo g (closedBall a r) (closedBall a r) := by
    intro x hx
    apply (IsUltrametricDist.dist_triangle_max (g x) (g a) a).trans
    apply max_le
    · exact (hgLip.dist_le_mul x hx a ha).trans
        ((mul_le_of_le_one_left dist_nonneg hc.le).trans hx)
    · rwa [hga]
  have hg : ContractingWith c (hgMap.restrict g _ _) := ⟨hc, hgLip.to_restrict⟩
  obtain ⟨x, hx, hfix, -⟩ :=
    hg.exists_fixedPoint' isClosed_closedBall.isComplete hgMap ha (edist_ne_top _ _)
  refine ⟨x, hx, ?_⟩
  change z - (f x - x) = x at hfix
  have heq : z = x + (f x - x) := sub_eq_iff_eq_add.mp hfix
  rw [add_comm x, sub_add_cancel] at heq
  exact heq.symm

variable [MeasurableSpace X] [BorelSpace X]

private theorem measure_closedBall_eq (μ : Measure X) [IsAddLeftInvariant μ]
    (a b : X) (r : ℝ) : μ (closedBall a r) = μ (closedBall b r) := by
  have h : (fun x => (a - b) + x) ⁻¹' closedBall a r = closedBall b r := by
    ext x
    change dist ((a - b) + x) a ≤ r ↔ dist x b ≤ r
    simpa only [sub_add_cancel] using
      (show dist ((a - b) + x) ((a - b) + b) ≤ r ↔ dist x b ≤ r by rw [dist_add_left])
  rw [← h, measure_preimage_add]

private theorem map_restrict_closedBall_of_approximatesLinearOn_id [ProperSpace X]
    (μ : Measure X) [IsAddLeftInvariant μ] [IsFiniteMeasureOnCompacts μ]
    {f : X → X} {a : X} {R : ℝ} {c : ℝ≥0}
    (hf : ApproximatesLinearOn f (ContinuousLinearMap.id K X) (closedBall a R) c)
    (hc : c < 1) (hR : 0 < R) :
    (μ.restrict (closedBall a R)).map f = μ.restrict (closedBall (f a) R) := by
  let B := closedBall a R
  let D := closedBall (f a) R
  have ha : a ∈ B := mem_closedBall_self hR.le
  have hdist {x y : X} (hx : x ∈ B) (hy : y ∈ B) :
      dist (f x) (f y) = dist x y := dist_eq_of_approximatesLinearOn_id hf hc hx hy
  have hmap : MapsTo f B D := fun x hx =>
    mem_closedBall.mpr ((hdist hx ha).le.trans hx)
  have hsurj : SurjOn f B D := surjOn_closedBall_of_approximatesLinearOn_id hf hc hR.le
  have hmeas : AEMeasurable f (μ.restrict B) :=
    aemeasurable_restrict_of_measurable_subtype isClosed_closedBall.measurableSet
      hf.continuous.measurable
  have : IsFiniteMeasure (μ.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall a R).measure_lt_top⟩
  let balls : Set (Set X) := {s | ∃ (b : X) (r : ℝ), 0 < r ∧ s = closedBall b r}
  have hbasis : TopologicalSpace.IsTopologicalBasis balls := by
    apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    · rintro _ ⟨b, r, hr, rfl⟩
      exact IsUltrametricDist.isOpen_closedBall b hr.ne'
    · intro b s hb hs
      obtain ⟨r, hr, hrs⟩ := nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hb)
      exact ⟨closedBall b r, ⟨b, r, hr, rfl⟩, mem_closedBall_self hr.le, hrs⟩
  have hpi : IsPiSystem balls := by
    rintro _ ⟨b, r, hr, rfl⟩ _ ⟨d, t, ht, rfl⟩ hinter
    rcases IsUltrametricDist.closedBall_subset_trichotomy (x := b) (y := d)
        (r := r) (s := t) with h | h | h
    · rw [inter_eq_left.mpr h]
      exact ⟨b, r, hr, rfl⟩
    · rw [inter_eq_right.mpr h]
      exact ⟨d, t, ht, rfl⟩
    · exact (hinter.not_disjoint h).elim
  refine ext_of_generate_finite balls (BorelSpace.measurable_eq.trans hbasis.borel_eq_generateFrom)
    hpi ?_ ?_
  · rintro _ ⟨b, r, _, rfl⟩
    rw [Measure.map_apply_of_aemeasurable hmeas isClosed_closedBall.measurableSet,
      Measure.restrict_apply' isClosed_closedBall.measurableSet,
      Measure.restrict_apply' isClosed_closedBall.measurableSet]
    change μ (f ⁻¹' closedBall b r ∩ B) = μ (closedBall b r ∩ D)
    by_cases h : (closedBall b r ∩ D).Nonempty
    · obtain ⟨z, hz, hzD⟩ := h
      obtain ⟨x, hx, rfl⟩ := hsurj hzD
      rw [IsUltrametricDist.closedBall_eq_of_mem hz]
      by_cases hr : r ≤ R
      · have hxsub : closedBall x r ⊆ B := by
          rw [show B = closedBall x R from IsUltrametricDist.closedBall_eq_of_mem hx]
          exact closedBall_subset_closedBall hr
        have hl : f ⁻¹' closedBall (f x) r ∩ B = closedBall x r := by
          ext y
          constructor
          · rintro ⟨hy, hyB⟩
            simpa only [mem_preimage, mem_closedBall, hdist hyB hx] using hy
          · intro hy
            have hyB := hxsub hy
            exact ⟨by simpa only [mem_preimage, mem_closedBall, hdist hyB hx] using hy, hyB⟩
        have hright : closedBall (f x) r ⊆ D := by
          rw [show D = closedBall (f x) R from IsUltrametricDist.closedBall_eq_of_mem hzD]
          exact closedBall_subset_closedBall hr
        rw [hl, inter_eq_left.mpr hright, measure_closedBall_eq μ x (f x) r]
      · have hright : D ⊆ closedBall (f x) r := by
          rw [show D = closedBall (f x) R from IsUltrametricDist.closedBall_eq_of_mem hzD]
          exact closedBall_subset_closedBall (le_of_not_ge hr)
        have hpre : B ⊆ f ⁻¹' closedBall (f x) r := fun _ hy => hright (hmap hy)
        rw [inter_eq_right.mpr hpre, inter_eq_right.mpr hright]
        exact measure_closedBall_eq μ a (f a) R
    · have hempty : f ⁻¹' closedBall b r ∩ B = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx, hxB⟩
        exact h ⟨f x, hx, hmap hxB⟩
      rw [hempty, not_nonempty_iff_eq_empty.mp h]
  · rw [Measure.map_apply_of_aemeasurable hmeas MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ, Measure.restrict_apply_univ]
    exact measure_closedBall_eq μ a (f a) R

variable [ProperSpace X]
  [NormedAddCommGroup Y] [NormedSpace K Y]
  [MeasurableSpace Y] [BorelSpace Y]

/-- Near a point with an invertible strict derivative, pushforward of additive Haar measure
on every sufficiently small closed ball equals the derivative's pushforward restricted to
the image. The map is bijective there onto the linear image of the corresponding ball. -/
theorem local_map_restrict_eq_of_hasStrictFDerivAt
    (μ : Measure X) [IsAddHaarMeasure μ]
    {f : X → Y} {a : X} (L : X ≃L[K] Y)
    (hf : HasStrictFDerivAt f (L : X →L[K] Y) a) :
    ∃ R : ℝ, 0 < R ∧ ∀ r ∈ Ioc 0 R,
      BijOn f (closedBall a r) (L '' closedBall (L.symm (f a)) r) ∧
      (μ.restrict (closedBall a r)).map f =
        (μ.map L).restrict (f '' closedBall a r) := by
  classical
  let g : X → X := L.symm ∘ f
  have hcomp : (L.symm : Y →L[K] X).comp (L : X →L[K] Y) =
      ContinuousLinearMap.id K X := by
    ext x
    exact L.symm_apply_apply x
  have hg : HasStrictFDerivAt g (ContinuousLinearMap.id K X) a := by
    rw [← hcomp]
    exact L.symm.hasStrictFDerivAt.comp a hf
  obtain ⟨s, hs, hs'⟩ := hg.approximates_deriv_on_nhds
    (c := 1 / 2) (Or.inr (by norm_num))
  obtain ⟨R, hR, hRs⟩ := nhds_basis_closedBall.mem_iff.mp hs
  refine ⟨R, hR, fun r hr => ?_⟩
  have hball := hs'.mono_set ((closedBall_subset_closedBall hr.2).trans hRs)
  have hc : (1 / 2 : ℝ≥0) < 1 := by norm_num
  have hmap := map_restrict_closedBall_of_approximatesLinearOn_id μ hball hc hr.1
  let B := closedBall a r
  let D := closedBall (g a) r
  have hdist {x y : X} (hx : x ∈ B) (hy : y ∈ B) : dist (g x) (g y) = dist x y :=
    dist_eq_of_approximatesLinearOn_id hball hc hx hy
  have hgBij : BijOn g B D := ⟨
    fun _ hx => mem_closedBall.mpr ((hdist hx (mem_closedBall_self hr.1.le)).le.trans hx),
    fun _ hx _ hy heq => dist_eq_zero.mp (by rw [← hdist hx hy, heq, dist_self]),
    surjOn_closedBall_of_approximatesLinearOn_id hball hc hr.1.le⟩
  have hfEq : f = L ∘ g := by
    funext x
    exact (L.apply_symm_apply (f x)).symm
  have hBij : BijOn f B (L '' D) := by
    rw [hfEq]
    exact L.injective.bijOn_image.comp hgBij
  refine ⟨hBij, ?_⟩
  have hge : g =ᵐ[μ.restrict B] B.piecewise g (fun _ => 0) := by
    filter_upwards [ae_restrict_mem (μ := μ) isClosed_closedBall.measurableSet] with x hx
    exact (piecewise_eq_of_mem B g _ hx).symm
  have hmeas : Measurable (B.piecewise g (fun _ => 0)) :=
    hball.continuousOn.measurable_piecewise continuous_const.continuousOn
      isClosed_closedBall.measurableSet
  have hL : Measurable L := L.continuous.measurable
  calc
    (μ.restrict B).map f = (μ.restrict B).map (L ∘ B.piecewise g (fun _ => 0)) :=
      Measure.map_congr (hfEq ▸ hge.fun_comp L)
    _ = ((μ.restrict B).map g).map L := by
      rw [← Measure.map_map hL hmeas, Measure.map_congr hge]
    _ = (μ.map L).restrict (L '' D) := by
      have hLemb : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
      rw [hmap, hLemb.restrict_map, preimage_image_eq _ L.injective]
    _ = (μ.map L).restrict (f '' B) := by rw [hBij.image_eq]

end Local

/-- In finite coordinates the local pushforward uses the inverse determinant factor. -/
theorem local_map_restrict_eq_inv_det_of_hasStrictFDerivAt
    {K ι : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] [Fintype ι] [DecidableEq ι]
    (ν : Measure K) [IsAddHaarMeasure ν] (χ : K →*₀ ℝ≥0)
    (hχ : ∀ z : K, z ≠ 0 → ν.map (fun x => z * x) = (χ z)⁻¹ • ν)
    (μ : Measure (ι → K)) [IsAddHaarMeasure μ]
    {f : (ι → K) → (ι → K)} {a : ι → K} (L : (ι → K) ≃L[K] (ι → K))
    (hf : HasStrictFDerivAt f (L : (ι → K) →L[K] (ι → K)) a) :
    ∃ R : ℝ, 0 < R ∧ ∀ r ∈ Ioc 0 R,
      BijOn f (closedBall a r) (L '' closedBall (L.symm (f a)) r) ∧
      (μ.restrict (closedBall a r)).map f =
        (χ (LinearMap.det (L.toLinearEquiv : (ι → K) →ₗ[K] (ι → K))))⁻¹ •
          μ.restrict (f '' closedBall a r) := by
  let M := LinearMap.toMatrix' (L.toLinearEquiv : (ι → K) →ₗ[K] (ι → K))
  have hdet : M.det = LinearMap.det (L.toLinearEquiv : (ι → K) →ₗ[K] (ι → K)) :=
    LinearMap.det_toMatrix' _
  have hL : (Matrix.toLin' M : (ι → K) → (ι → K)) = L := by
    change ((LinearMap.toMatrix').symm
      (LinearMap.toMatrix' (L.toLinearEquiv : (ι → K) →ₗ[K] (ι → K))) :
      (ι → K) → (ι → K)) = L
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hmap := Langlands.HarmonicAnalysis.haarMeasure_map_matrix ν χ hχ μ
    (hdet ▸ L.toLinearEquiv.isUnit_det'.ne_zero : M.det ≠ 0)
  rw [hL, hdet] at hmap
  obtain ⟨R, hR, h⟩ := local_map_restrict_eq_of_hasStrictFDerivAt μ L hf
  refine ⟨R, hR, fun r hr => ?_⟩
  obtain ⟨hBij, hmeasure⟩ := h r hr
  exact ⟨hBij, by rw [hmeasure, hmap, Measure.restrict_smul]⟩

/-- The local change-of-variables law on proper ultrametric normed spaces. -/
def NonarchimedeanChangeOfVariablesStatement : Prop :=
  ∀ (K : Type u) (X : Type v) (Y : Type w) [NontriviallyNormedField K]
    [NormedAddCommGroup X] [NormedSpace K X] [IsUltrametricDist X] [ProperSpace X]
    [NormedAddCommGroup Y] [NormedSpace K Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [IsAddHaarMeasure μ] (f : X → Y) (a : X) (L : X ≃L[K] Y),
    HasStrictFDerivAt f (L : X →L[K] Y) a →
      ∃ R : ℝ, 0 < R ∧ ∀ r ∈ Ioc 0 R,
        BijOn f (closedBall a r) (L '' closedBall (L.symm (f a)) r) ∧
        (μ.restrict (closedBall a r)).map f =
          (μ.map L).restrict (f '' closedBall a r)

/-- The local Haar change of variables for an invertible strict derivative. -/
theorem nonarchimedeanChangeOfVariables : NonarchimedeanChangeOfVariablesStatement.{u, v, w} := by
  intro K X Y _ _ _ _ _ _ _ _ _ _ _ μ _ f a L hf
  exact local_map_restrict_eq_of_hasStrictFDerivAt μ L hf

end Langlands.Analysis
