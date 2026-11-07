import Langlands.Analysis.CompactManifoldWeightedIntegralStatement
import Langlands.Analysis.CompactWeightedIntegral
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

universe uX uV uM uH uN uE

namespace Langlands.Analysis

open MeasureTheory Set
open scoped Manifold ContDiff

variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold 𝓘(ℝ, H) ∞ N]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (μ : Measure X) [IsFiniteMeasure μ] (w : C(X, E)) (j : C(X, N))

/-- The coordinate reduction when the compact image lies in one integration chart. -/
theorem contDiffOn_compactWeightedIntegral_of_chart
    (s : Set V) (hs : IsOpen s) (z : N)
    (hj : ∀ x, j x ∈ (chartAt H z).source)
    (h : V × N → ℂ)
    (hh : ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, ℂ) ∞ h (s ×ˢ univ)) :
    (∀ p ∈ s, Integrable (fun x => h (p, j x) • w x) μ) ∧
      ContDiffOn ℝ ∞ (fun p => ∫ x, h (p, j x) • w x ∂μ) s := by
  classical
  let c := chartAt H z
  let jc : C(X, H) := ⟨fun x => c (j x),
    c.continuousOn_toFun.comp_continuous j.continuous hj⟩
  have hjc : ∀ x, jc x ∈ c.target := fun x => c.map_source (hj x)
  let hc : V × H → ℂ := fun q => h (q.1, c.symm q.2)
  have hci : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, H) ∞ c.symm c.target :=
    contMDiffOn_chart_symm
  have hcoord : ContDiffOn ℝ ∞ hc (s ×ˢ c.target) := by
    have hid : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, V) ∞ id s := contMDiff_id.contMDiffOn
    have hp := hh.comp (hid.prodMap hci) (fun q hq => ⟨hq.1, mem_univ _⟩)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hp
    exact hp.contDiffOn
  let f (p : V) : C(X, ℂ) :=
    if hp : p ∈ s then
      ⟨fun x => hc (p, jc x), hcoord.continuousOn.comp_continuous
        (continuous_const.prodMk jc.continuous) (fun x => ⟨hp, hjc x⟩)⟩
    else 0
  have heq : ∀ p ∈ s, ∀ x, f p x = hc (p, jc x) := by
    intro p hp x
    simp only [f, dite_eq_left hp, ContinuousMap.coe_mk]
  have heq' : ∀ p ∈ s, ∀ x, f p x = h (p, j x) := by
    intro p hp x
    rw [heq p hp]
    change h (p, c.symm (c (j x))) = _
    rw [c.left_inv (hj x)]
  have hf : ContDiffOn ℝ ∞ f s :=
    contDiffOn_infty_compactFamily_of_joint jc hs c.open_target hjc hcoord heq
  constructor
  · intro p hp
    simpa only [heq' p hp] using compactWeightedIntegral_integrable μ w (f p)
  · have hI := (compactWeightedIntegral μ w).restrictScalars ℝ |>.contDiff.comp_contDiffOn hf
    apply hI.congr
    intro p hp
    exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
      congrArg (fun a : ℂ => a • w x) (heq' p hp x).symm)


/-- A finite continuous partition reduces an arbitrary compact image to chart pieces. -/
theorem contDiffOn_compactWeightedIntegral [T2Space X]
    (s : Set V) (hs : IsOpen s) (h : V × N → ℂ)
    (hh : ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, ℂ) ∞ h (s ×ˢ univ)) :
    (∀ p ∈ s, Integrable (fun x => h (p, j x) • w x) μ) ∧
      ContDiffOn ℝ ∞ (fun p => ∫ x, h (p, j x) • w x ∂μ) s := by
  classical
  have hc (p : V) (hp : p ∈ s) : Continuous (fun x => h (p, j x)) :=
    hh.continuousOn.comp_continuous (continuous_const.prodMk j.continuous)
      (fun _ => ⟨hp, mem_univ _⟩)
  have hi (p : V) (hp : p ∈ s) : Integrable (fun x => h (p, j x) • w x) μ :=
    ((hc p hp).smul w.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine ⟨hi, ?_⟩
  let U (z : N) : Set X := j ⁻¹' (chartAt H z).source
  have hUo (z : N) : IsOpen (U z) :=
    (chartAt H z).open_source.preimage j.continuous
  have hUc : (univ : Set X) ⊆ ⋃ z, U z := by
    intro x _
    exact mem_iUnion.mpr ⟨j x, mem_chart_source H (j x)⟩
  obtain ⟨a, ha⟩ := isCompact_univ.elim_finite_subcover U hUo hUc
  have hUa : (univ : Set X) ⊆ ⋃ z : a, U z.val := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := mem_iUnion₂.mp (ha hx)
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, hzx⟩
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite
    isClosed_univ (fun z : a => U z.val) (fun z => hUo z.val)
    (locallyFinite_of_finite _) hUa
  let K (i : a) : Set X := tsupport (f i)
  have hK (i : a) : IsClosed (K i) := isClosed_tsupport _
  let (i : a) : CompactSpace (K i) := isCompact_iff_compactSpace.mp (hK i).isCompact
  let wi (i : a) : C(K i, E) :=
    ⟨fun x => f i x.val • w x.val,
      ((f i).continuous.comp continuous_subtype_val).smul
        (w.continuous.comp continuous_subtype_val)⟩
  let ji (i : a) : C(K i, N) := j.comp ⟨Subtype.val, continuous_subtype_val⟩
  let G (i : a) (p : V) : E :=
    ∫ x : K i, h (p, ji i x) • wi i x ∂(μ.comap Subtype.val)
  have hG (i : a) : ContDiffOn ℝ ∞ (G i) s := by
    apply (contDiffOn_compactWeightedIntegral_of_chart
      (μ.comap Subtype.val) (wi i) (ji i) s hs i.val ?_ h hh).2
    intro x
    exact hf i x.property
  have hFi (p : V) (hp : p ∈ s) (i : a) :
      Integrable (fun x => h (p, j x) • (f i x • w x)) μ :=
    ((hc p hp).smul ((f i).continuous.smul w.continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hGeq (i : a) (p : V) :
      G i p = ∫ x, h (p, j x) • (f i x • w x) ∂μ := by
    change (∫ x : K i, h (p, j x.val) • (f i x.val • w x.val) ∂(μ.comap Subtype.val)) = _
    rw [integral_subtype_comap (μ := μ) (hK i).measurableSet
      (fun x => h (p, j x) • (f i x • w x))]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : f i x = 0 := by
      by_contra hz
      exact hx (subset_tsupport (f i) (Function.mem_support.mpr hz))
    rw [hz, zero_smul, smul_zero]
  have heq (p : V) (hp : p ∈ s) :
      (∫ x, h (p, j x) • w x ∂μ) = ∑ i : a, G i p := by
    calc
      (∫ x, h (p, j x) • w x ∂μ) =
          ∫ x, ∑ i : a, h (p, j x) • (f i x • w x) ∂μ := by
        apply integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro x
        have hsum : ∑ i : a, f i x = 1 := by
          simpa only [finsum_eq_sum_of_fintype] using f.sum_eq_one (mem_univ x)
        simp only [smul_comm (h (p, j x)), ← Finset.sum_smul, hsum, one_smul]
      _ = ∑ i : a, ∫ x, h (p, j x) • (f i x • w x) ∂μ :=
        integral_finsetSum _ (fun i _ => hFi p hp i)
      _ = ∑ i : a, G i p := Finset.sum_congr rfl (fun i _ => (hGeq i p).symm)
  apply (ContDiffOn.sum (fun i _ => hG i)).congr
  exact heq


/-- The full manifold theorem follows from finite integration-chart partitions
and locality in the original parameter charts. -/
theorem compactManifoldWeightedIntegral :
    CompactManifoldWeightedIntegralStatement.{uX,uV,uM,uH,uN,uE} := by
  intro X _ _ _ _ _ V _ _ M _ _ _ H _ _ N _ _ _ E _ _ _ μ _ w j h hh
  constructor
  · intro p
    exact ((hh.continuous.comp (continuous_const.prodMk j.continuous)).smul
      w.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro p
    let c := extChartAt 𝓘(ℝ, V) p
    have hct : IsOpen c.target := (chartAt V p).isOpen_extend_target
    have hci : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, V) ∞ c.symm c.target :=
      contMDiffOn_extChartAt_symm p
    have hid : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, H) ∞ (id : N → N) univ :=
      contMDiff_id.contMDiffOn
    have hk : ContMDiffOn (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, ℂ) ∞
        (fun q : V × N => h (c.symm q.1, q.2)) (c.target ×ˢ univ) :=
      hh.comp_contMDiffOn (hci.prodMap hid)
    have hs := (contDiffOn_compactWeightedIntegral μ w j c.target hct _ hk).2
    rw [contMDiffAt_iff_source, ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ]
    exact (hs.contDiffAt (hct.mem_nhds (mem_extChartAt_target p))).contMDiffAt

end Langlands.Analysis
