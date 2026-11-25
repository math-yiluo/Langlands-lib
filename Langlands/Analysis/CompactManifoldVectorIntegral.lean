import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Compact integration of vector-valued smooth manifold families -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped Manifold ContDiff Topology

namespace Langlands.Analysis.CompactManifoldVectorIntegral

universe uX uV uM uH uN uE

variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (μ : Measure X) [IsFiniteMeasure μ]

omit [CompleteSpace E] in
/-- Joint continuity of a proposed partial derivative on a compact integration
space supplies the local bound needed for genuine differentiation under the integral. -/
theorem hasFDerivAt_integral {s : Set V} (hs : IsOpen s)
    {F : V → X → E} {D : V → X → V →L[ℝ] E}
    (hF : ContinuousOn (Function.uncurry F) (s ×ˢ univ))
    (hD : ContinuousOn (Function.uncurry D) (s ×ˢ univ))
    (hd : ∀ p ∈ s, ∀ x, HasFDerivAt (fun q => F q x) (D p x) p)
    {p : V} (hp : p ∈ s) :
    HasFDerivAt (fun q => ∫ x, F q x ∂μ) (∫ x, D p x ∂μ) p := by
  have hcF (q : V) (hq : q ∈ s) : Continuous (F q) :=
    hF.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨hq, mem_univ _⟩)
  have hcD (q : V) (hq : q ∈ s) : Continuous (D q) :=
    hD.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨hq, mem_univ _⟩)
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hs p hp
  have hcb : closedBall p (ε / 2) ⊆ s :=
    (closedBall_subset_ball (half_lt_self hε)).trans hb
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall p (ε / 2)).prod isCompact_univ).exists_bound_of_continuousOn
      (hD.mono (prod_mono hcb subset_rfl))
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := ball p (ε / 2)) (F' := D) (bound := fun _ => C)
    (ball_mem_nhds p (half_pos hε)) ?_ ?_ ?_ ?_ (integrable_const C) ?_
  · filter_upwards [hs.mem_nhds hp] with q hq
    exact ((hcF q hq).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).aestronglyMeasurable
  · exact (hcF p hp).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact ((hcD p hp).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x q hq =>
      hC (q, x) ⟨ball_subset_closedBall hq, mem_univ _⟩
  · exact Filter.Eventually.of_forall fun x q hq => hd q (hcb (ball_subset_closedBall hq)) x

variable {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold 𝓘(ℝ, H) ∞ N]

omit [FiniteDimensional ℝ V] [CompleteSpace E] in
/-- The actual partial derivative in the vector parameter is smooth jointly with
the manifold parameter on an open parameter domain. -/
theorem contMDiffOn_partialFDeriv {s : Set V} (hs : IsOpen s) {h : V × N → E}
    (hh : ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞ h (s ×ˢ univ)) :
    ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, V →L[ℝ] E) ∞
      (fun p : V × N => fderiv ℝ (fun q => h (q, p.2)) p.1) (s ×ˢ univ) := by
  intro p hp
  have hhp : ContMDiffAt (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞ h p :=
    (hh p hp).contMDiffAt ((hs.prod isOpen_univ).mem_nhds hp)
  have hf : ContMDiffAt ((𝓘(ℝ, V).prod 𝓘(ℝ, H)).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞
      (fun q : (V × N) × V => h (q.2, q.1.2)) (p, p.1) :=
    hhp.comp (p, p.1) (contMDiffAt_snd.prodMk (contMDiffAt_snd.comp _ contMDiffAt_fst))
  have hd := hf.mfderiv (m := ∞)
    (fun p : V × N => fun q : V => h (q, p.2)) (fun p : V × N => p.1)
    contMDiffAt_fst (by simp)
  simp only [inTangentCoordinates_model_space, mfderiv_eq_fderiv] at hd
  erw [inTangentCoordinates_model_space] at hd
  exact hd.contMDiffWithinAt

variable (a : C(X, ℂ)) (j : C(X, N))

omit [CompleteSpace E] in
/-- The first vector-parameter derivative of the original weighted integral is
the integral of its actual partial derivative. -/
theorem hasFDerivAt_weightedIntegral {s : Set V} (hs : IsOpen s) {h : V × N → E}
    (hh : ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞ h (s ×ˢ univ))
    {p : V} (hp : p ∈ s) :
    HasFDerivAt (fun q => ∫ x, a x • h (q, j x) ∂μ)
      (∫ x, a x • fderiv ℝ (fun q => h (q, j x)) p ∂μ) p := by
  have hJ : Continuous (fun p : V × X => (p.1, j p.2)) :=
    continuous_fst.prodMk (j.continuous.comp continuous_snd)
  have hd := contMDiffOn_partialFDeriv hs hh
  apply hasFDerivAt_integral μ hs
    (F := fun q x => a x • h (q, j x))
    (D := fun q x => a x • fderiv ℝ (fun q => h (q, j x)) q)
    ((a.continuous.comp continuous_snd).continuousOn.smul
      (hh.continuousOn.comp hJ.continuousOn (fun p hp => ⟨hp.1, mem_univ _⟩)))
    ((a.continuous.comp continuous_snd).continuousOn.smul
      (hd.continuousOn.comp hJ.continuousOn (fun p hp => ⟨hp.1, mem_univ _⟩)))
  · intro q hq x
    have hslice : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, E) ∞
        (fun q => h (q, j x)) q :=
      ((hh (q, j x) ⟨hq, mem_univ _⟩).contMDiffAt
        ((hs.prod isOpen_univ).mem_nhds ⟨hq, mem_univ _⟩)).comp q
          (contMDiffAt_id.prodMk contMDiffAt_const)
    exact (hslice.contDiffAt.differentiableAt (by simp)).hasFDerivAt.const_smul (a x)
  · exact hp

omit [CompleteSpace E] in
/-- Every finite smoothness order follows by induction through actual directional
derivatives, with the original vector-valued codomain fixed. -/
theorem contDiffOn_weightedIntegral_nat {s : Set V} (hs : IsOpen s) (n : ℕ) :
    ∀ (h : V × N → E),
      ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞ h (s ×ˢ univ) →
      ContDiffOn ℝ n (fun p => ∫ x, a x • h (p, j x) ∂μ) s := by
  induction n with
  | zero =>
      intro h hh
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun p hp =>
        (hasFDerivAt_weightedIntegral μ a j hs hh hp).continuousAt.continuousWithinAt
  | succ n ih =>
      intro h hh
      have hD := fun p (hp : p ∈ s) =>
        hasFDerivAt_weightedIntegral μ a j hs hh hp
      rw [Nat.cast_succ]
      refine contDiffOn_succ_of_fderiv_apply
        (fun p hp => (hD p hp).differentiableAt.differentiableWithinAt)
        (fun h => by simp at h) fun v => ?_
      have hd := contMDiffOn_partialFDeriv hs hh
      have hdir : ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
          (fun p : V × N => fderiv ℝ (fun q => h (q, p.2)) p.1 v)
          (s ×ˢ univ) :=
        hd.clm_apply contMDiffOn_const
      refine (ih _ hdir).congr fun p hp => ?_
      have hc : Continuous (fun x => a x • fderiv ℝ (fun q => h (q, j x)) p) :=
        a.continuous.smul
          (hd.continuousOn.comp_continuous
            (continuous_const.prodMk j.continuous) (fun _ => ⟨hp, mem_univ _⟩))
      have hi := hc.integrable_of_hasCompactSupport (μ := μ)
        (HasCompactSupport.of_compactSpace _)
      rw [fderivWithin_of_isOpen hs hp, (hD p hp).fderiv,
        ContinuousLinearMap.integral_apply hi]
      rfl

omit [CompleteSpace E] in
/-- A continuous compact restriction and a continuous fixed scalar weight
preserve all orders of smoothness in a finite-dimensional vector parameter. -/
theorem contDiffOn_weightedIntegral {s : Set V} (hs : IsOpen s) {h : V × N → E}
    (hh : ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞ h (s ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p => ∫ x, a x • h (p, j x) ∂μ) s :=
  contDiffOn_infty.mpr fun n => contDiffOn_weightedIntegral_nat μ a j hs n h hh

variable {M : Type uM} [TopologicalSpace M] [ChartedSpace V M]
  [IsManifold 𝓘(ℝ, V) ∞ M]

omit [CompleteSpace E] in
/-- Compact integration preserves smoothness in a manifold parameter with
finite-dimensional real model. -/
theorem contMDiff_weightedIntegral {h : M × N → E}
    (hh : ContMDiff (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞ h) :
    ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ (fun p => ∫ x, a x • h (p, j x) ∂μ) := by
  intro p
  let c := extChartAt 𝓘(ℝ, V) p
  have hct : IsOpen c.target := (chartAt V p).isOpen_extend_target
  have hci : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, V) ∞ c.symm c.target :=
    contMDiffOn_extChartAt_symm p
  have hid : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, H) ∞ (id : N → N) univ :=
    contMDiff_id.contMDiffOn
  have hk : ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
      (fun q : V × N => h (c.symm q.1, q.2)) (c.target ×ˢ univ) :=
    hh.comp_contMDiffOn (hci.prodMap hid)
  have hs := contDiffOn_weightedIntegral μ a j hct hk
  rw [contMDiffAt_iff_source, ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ]
  exact (hs.contDiffAt (hct.mem_nhds (mem_extChartAt_target p))).contMDiffAt

set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional ℝ V] [CompleteSpace E] [IsManifold 𝓘(ℝ, V) ∞ M] in
/-- With a vector target and a boundaryless real model, the manifold derivative
is the derivative of the original function in its source chart. -/
theorem mfderiv_eq_fderiv_chart {f : M → E} {p : M}
    (hf : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) f p) :
    mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f p =
      fderiv ℝ (fun q => f ((extChartAt 𝓘(ℝ, V) p).symm q))
        (extChartAt 𝓘(ℝ, V) p p) := by
  simpa only [ModelWithCorners.range_eq_univ, fderivWithin_univ,
    writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp, Function.comp_def, id_eq] using hf.mfderiv_abuse

set_option backward.isDefEq.respectTransparency false in
omit [CompleteSpace E] in
/-- The actual manifold derivative of the weighted integral is the integral
of the actual manifold derivatives of its original integrand. -/
theorem mfderiv_weightedIntegral {h : M × N → E}
    (hh : ContMDiff (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞ h) (p : M) :
    @Eq (V →L[ℝ] E)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (fun q => ∫ x, a x • h (q, j x) ∂μ) p)
      (∫ x, a x •
        (show V →L[ℝ] E from
          mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (fun q => h (q, j x)) p) ∂μ) := by
  let c := extChartAt 𝓘(ℝ, V) p
  have hct : IsOpen c.target := (chartAt V p).isOpen_extend_target
  have hci : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, V) ∞ c.symm c.target :=
    contMDiffOn_extChartAt_symm p
  have hid : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, H) ∞ (id : N → N) univ :=
    contMDiff_id.contMDiffOn
  have hk : ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
      (fun q : V × N => h (c.symm q.1, q.2)) (c.target ×ˢ univ) :=
    hh.comp_contMDiffOn (hci.prodMap hid)
  rw [mfderiv_eq_fderiv_chart
    ((contMDiff_weightedIntegral μ a j hh p).mdifferentiableAt (by simp))]
  rw [(hasFDerivAt_weightedIntegral μ a j hct hk (mem_extChartAt_target p)).fderiv]
  apply integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  congr 1
  exact (mfderiv_eq_fderiv_chart
    ((hh.comp (contMDiff_id.prodMk contMDiff_const) p).mdifferentiableAt (by simp))).symm

set_option backward.isDefEq.respectTransparency false in
omit [CompleteSpace E] in
/-- Evaluating the genuine manifold derivative commutes with the same
weighted integral. -/
theorem mfderiv_weightedIntegral_apply {h : M × N → E}
    (hh : ContMDiff (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞ h) (p : M) (v : V) :
    @Eq E
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (fun q => ∫ x, a x • h (q, j x) ∂μ) p v)
      (∫ x, a x • (show E from
        mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (fun q => h (q, j x)) p v) ∂μ) := by
  let c := extChartAt 𝓘(ℝ, V) p
  have hct : IsOpen c.target := (chartAt V p).isOpen_extend_target
  have hk : ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞
      (fun q : V × N => h (c.symm q.1, q.2)) (c.target ×ˢ univ) :=
    hh.comp_contMDiffOn ((contMDiffOn_extChartAt_symm p).prodMap
      (contMDiff_id.contMDiffOn : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, H) ∞ (id : N → N) univ))
  have hd := contMDiffOn_partialFDeriv hct hk
  have hc : Continuous (fun x => a x •
      fderiv ℝ (fun q => h (c.symm q, j x)) (c p)) :=
    a.continuous.smul (hd.continuousOn.comp_continuous
      (continuous_const.prodMk j.continuous)
        (fun _ => ⟨mem_extChartAt_target p, mem_univ _⟩))
  have hi : Integrable (fun x => a x •
      (show V →L[ℝ] E from mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (fun q => h (q, j x)) p)) μ := by
    apply (hc.integrable_of_hasCompactSupport (μ := μ)
      (HasCompactSupport.of_compactSpace _)).congr
    apply Filter.Eventually.of_forall
    intro x
    exact congrArg (fun L : V →L[ℝ] E => a x • L)
      (mfderiv_eq_fderiv_chart (f := fun q => h (q, j x))
        ((hh.comp (contMDiff_id.prodMk contMDiff_const) p).mdifferentiableAt
          (by simp))).symm
  change (show V →L[ℝ] E from
    mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (fun q => ∫ x, a x • h (q, j x) ∂μ) p) v = _
  rw [mfderiv_weightedIntegral μ a j hh p, ContinuousLinearMap.integral_apply hi]
  rfl

end Langlands.Analysis.CompactManifoldVectorIntegral

namespace Langlands.Analysis

universe uX uV uM uH uN uE

/-- Compact integration of a jointly smooth Banach-valued family preserves
smoothness and commutes with the genuine manifold derivative, both as an
identity of continuous linear maps and after evaluation on a model vector. -/
def CompactManifoldVectorIntegralStatement : Prop :=
  ∀ (X : Type uX) [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (M : Type uM) [TopologicalSpace M] [ChartedSpace V M]
    [IsManifold 𝓘(ℝ, V) ∞ M]
    (H : Type uH) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (N : Type uN) [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold 𝓘(ℝ, H) ∞ N]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure X) [IsFiniteMeasure μ]
    (a : C(X, ℂ)) (j : C(X, N)) (h : M × N → E),
    ContMDiff (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, E) ∞ h →
    (∀ p : M, Integrable (fun x => a x • h (p, j x)) μ) ∧
      ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞
        (fun p : M => ∫ x, a x • h (p, j x) ∂μ) ∧
      (∀ p : M, @Eq (V →L[ℝ] E)
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (fun q => ∫ x, a x • h (q, j x) ∂μ) p)
        (∫ x, a x • (show V →L[ℝ] E from
          mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (fun q => h (q, j x)) p) ∂μ)) ∧
      ∀ (p : M) (v : V), @Eq E
        (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (fun q => ∫ x, a x • h (q, j x) ∂μ) p v)
        (∫ x, a x • (show E from
          mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (fun q => h (q, j x)) p v) ∂μ)

/-- The compact vector-integral assertion, proved from dominated
differentiation and local source charts. -/
theorem compactManifoldVectorIntegral :
    CompactManifoldVectorIntegralStatement.{uX,uV,uM,uH,uN,uE} := by
  intro X _ _ _ _ V _ _ _ M _ _ _ H _ _ N _ _ _ E _ _ _ μ _ a j h hh
  refine ⟨?_, CompactManifoldVectorIntegral.contMDiff_weightedIntegral μ a j hh,
    CompactManifoldVectorIntegral.mfderiv_weightedIntegral μ a j hh,
    CompactManifoldVectorIntegral.mfderiv_weightedIntegral_apply μ a j hh⟩
  intro p
  exact (a.continuous.smul
    (hh.continuous.comp (continuous_const.prodMk j.continuous))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end Langlands.Analysis
