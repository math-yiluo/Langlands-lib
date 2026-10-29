import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Langlands.Group.GL.UpperUnipotentCompactContainmentProof
import Langlands.Group.GL.CountabilityProof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.Representation.RankinSelberg.TwoBlockDeformationNonvanishing

/-!
# Auxiliary analysis for the two-block deformation

General facts used to prove that the deformed Whittaker functions are entire:
an entire function vanishing on an uncountable set vanishes; the same for finite
exponential sums `∑ b_i^u • w_i` with positive real bases in any complex vector space;
the integral `u ↦ ∫_K α β^u` over a compact set with `β` positive and locally constant
is entire. It also records that the inverse standard character has open kernel, that
the upper unipotent group has an increasing exhaustion by compact open subgroups, and
that the rectangular matrices have an exhaustion by compact sets.
-/

noncomputable section

open MeasureTheory Topology Filter

namespace Langlands.RankinSelberg.TwoBlockDeformation

open HarmonicAnalysis Whittaker GeneralLinear

universe uF

section Complex

/-- An uncountable set of complex numbers has an accumulation point. -/
theorem exists_accPt_of_not_countable {S : Set ℂ} (hS : ¬ S.Countable) :
    ∃ z, AccPt z (𝓟 S) := by
  have hinf : ∃ n : ℕ, (S ∩ Metric.closedBall 0 n).Infinite := by
    by_contra hcon
    simp only [not_exists, Set.not_infinite] at hcon
    apply hS
    have hS' : S = ⋃ n : ℕ, S ∩ Metric.closedBall 0 n := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
      constructor
      · intro hz
        obtain ⟨n, hn⟩ := exists_nat_ge ‖z‖
        exact ⟨n, hz, hn⟩
      · rintro ⟨n, hz, -⟩
        exact hz
    rw [hS']
    exact Set.countable_iUnion fun n => (hcon n).countable
  obtain ⟨n, hn⟩ := hinf
  obtain ⟨z, -, hz⟩ :=
    hn.exists_accPt_of_subset_isCompact (isCompact_closedBall 0 n) Set.inter_subset_right
  exact ⟨z, hz.mono (principal_mono.mpr Set.inter_subset_left)⟩

/-- An entire function vanishing on an uncountable set vanishes identically. -/
theorem eq_zero_of_not_countable {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : ¬ {u | f u = 0}.Countable) (u : ℂ) : f u = 0 := by
  obtain ⟨z, hz⟩ := exists_accPt_of_not_countable h
  have hfr : ∃ᶠ w in 𝓝[≠] z, f w = 0 := accPt_iff_frequently_nhdsNE.mp hz
  have han : AnalyticOnNhd ℂ f Set.univ := fun w _ => hf.analyticAt w
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ z) hfr (Set.mem_univ u)

/-- `u ↦ b^u` is entire for a positive real base `b`. -/
theorem differentiable_ofReal_cpow {b : ℝ} (hb : 0 < b) :
    Differentiable ℂ (fun u : ℂ => (b : ℂ) ^ u) :=
  differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hb.ne'))

/-- A finite exponential sum `∑ b_i^u • w_i` with positive real bases in a complex vector
space that vanishes for uncountably many `u` vanishes for every `u`. -/
theorem sum_cpow_smul_eq_zero_of_not_countable {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} (s : Finset ι) (b : ι → ℝ) (hb : ∀ i, 0 < b i) (w : ι → V)
    (h : ¬ {u : ℂ | ∑ i ∈ s, ((b i : ℂ) ^ u) • w i = 0}.Countable) (u : ℂ) :
    ∑ i ∈ s, ((b i : ℂ) ^ u) • w i = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have hd : Differentiable ℂ (fun u : ℂ => φ (∑ i ∈ s, ((b i : ℂ) ^ u) • w i)) := by
    simp only [map_sum, map_smul, smul_eq_mul]
    exact Differentiable.fun_sum fun i _ => (differentiable_ofReal_cpow (hb i)).mul_const _
  refine eq_zero_of_not_countable hd (fun hc => h (hc.mono fun v hv => ?_)) u
  simp only [Set.mem_ofPred_eq] at hv ⊢
  rw [hv, map_zero]

end Complex

section Integral

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- For a compact set `K`, a function `α` integrable on `K` and a positive locally constant
function `β`, the integral `u ↦ ∫_K α β^u` is entire. On `K`, `β` takes finitely many
values `b`, and the integral is `∑_b b^u ∫_{K ∩ β⁻¹(b)} α`. -/
theorem differentiable_setIntegral_mul_cpow (μ : Measure X) {K : Set X} (hK : IsCompact K)
    {β : X → ℝ} (hβ : IsLocallyConstant β) (hβpos : ∀ x, 0 < β x) {α : X → ℂ}
    (hα : IntegrableOn α K μ) :
    Differentiable ℂ (fun u : ℂ => ∫ x in K, α x * (β x : ℂ) ^ u ∂μ) := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hfin : (β '' K).Finite := by
    rw [Set.image_eq_range]
    exact (hβ.comp_continuous continuous_subtype_val).range_finite
  let S := hfin.toFinset
  let s : ℝ → Set X := fun b => K ∩ β ⁻¹' {b}
  have hmeas : ∀ b ∈ S, MeasurableSet (s b) := fun b _ =>
    hK.isClosed.measurableSet.inter (hβ.isOpen_fiber b).measurableSet
  have hdisj : Set.Pairwise (↑S) (Function.onFun Disjoint s) := by
    intro b _ c _ hbc
    exact Set.disjoint_left.mpr fun x hxb hxc => hbc (hxb.2.symm.trans hxc.2)
  have hK' : K = ⋃ b ∈ S, s b := by
    ext x
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, s, S, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hx
      exact ⟨β x, ⟨x, hx, rfl⟩, hx, rfl⟩
    · rintro ⟨_, _, hx, _⟩
      exact hx
  have hpos : ∀ b ∈ S, 0 < b := by
    intro b hb
    obtain ⟨x, -, rfl⟩ := hfin.mem_toFinset.mp hb
    exact hβpos x
  have key : ∀ u : ℂ, ∫ x in K, α x * (β x : ℂ) ^ u ∂μ =
      ∑ b ∈ S, (b : ℂ) ^ u * ∫ x in s b, α x ∂μ := by
    intro u
    calc ∫ x in K, α x * (β x : ℂ) ^ u ∂μ
        = ∫ x in ⋃ b ∈ S, s b, α x * (β x : ℂ) ^ u ∂μ := by rw [← hK']
      _ = ∑ b ∈ S, ∫ x in s b, α x * (β x : ℂ) ^ u ∂μ := by
          refine integral_biUnion_finset S hmeas hdisj fun b hb => ?_
          have hc : IntegrableOn (fun x => α x * (b : ℂ) ^ u) (s b) μ :=
            (hα.mono_set Set.inter_subset_left).mul_const _
          refine hc.congr_fun (fun x hx => ?_) (hmeas b hb)
          change α x * (b : ℂ) ^ u = α x * (β x : ℂ) ^ u
          rw [show β x = b from hx.2]
      _ = ∑ b ∈ S, (b : ℂ) ^ u * ∫ x in s b, α x ∂μ := by
          refine Finset.sum_congr rfl fun b hb => ?_
          rw [← integral_const_mul]
          refine setIntegral_congr_fun (hmeas b hb) fun x hx => ?_
          change α x * (β x : ℂ) ^ u = (b : ℂ) ^ u * α x
          rw [show β x = b from hx.2, mul_comm]
  rw [funext key]
  exact Differentiable.fun_sum fun b hb => (differentiable_ofReal_cpow (hpos b hb)).mul_const _

end Integral

section Group

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The inverse standard character of the upper unipotent group has open kernel. -/
theorem isOpen_ker_inverseStandardCharacter
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (n : ℕ) :
    letI := F.canonicalTopologicalData.topology
    IsOpen ((inverseStandardCharacter ψ n).ker : Set (upperUnipotent (n + 1) F.Carrier)) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (n + 1)
  let σ : upperUnipotent (n + 1) F.Carrier → F.Carrier := fun g =>
    ∑ k : Fin n, g.val k.castSucc k.succ
  have hc : Continuous σ :=
    continuous_finsetSum _ fun k _ => (UpperUnipotent.entry k.castSucc k.succ).continuous
  have h0 : σ 1 = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    change (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) k.castSucc k.succ = 0
    exact Matrix.one_apply_ne (ne_of_lt Fin.castSucc_lt_succ)
  have hU : σ ⁻¹' {y : F.Carrier | ψ.complex y = 1} ∈ 𝓝 (1 : upperUnipotent (n + 1) F.Carrier) :=
    hc.continuousAt.preimage_mem_nhds (h0 ▸ character_eq_one_mem_nhds F ψ)
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  filter_upwards [hU] with g hg
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  apply Units.ext
  rw [inverseStandardCharacter_apply]
  change (ψ.complex (σ g))⁻¹ = 1
  rw [show ψ.complex (σ g) = 1 from hg, inv_one]

/-- The upper unipotent group has an increasing exhaustion by compact open subgroups. -/
theorem exists_upperUnipotent_exhaustion (n : ℕ) :
    letI := F.canonicalTopologicalData.topology
    ∃ S : ℕ → OpenSubgroup (upperUnipotent n F.Carrier),
      (∀ k, IsCompact (S k : Set (upperUnipotent n F.Carrier))) ∧ Monotone S ∧
        ∀ g : upperUnipotent n F.Carrier, ∃ k, g ∈ S k := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearSigmaCompactSpace n
  have : SigmaCompactSpace (upperUnipotent n F.Carrier) :=
    (UpperUnipotent.isClosed (R := F.Carrier) (n := n)).sigmaCompactSpace
  let U := upperUnipotent n F.Carrier
  let Q := {K : OpenSubgroup U // IsCompact (K : Set U)}
  have step : ∀ C : Set U, IsCompact C → ∃ K : Q, C ⊆ (K.val : Set U) := by
    intro C hC
    obtain ⟨K, hK, hCK⟩ := upperUnipotentCompactContainment p inferInstance F T n C hC
    exact ⟨⟨K, hK⟩, hCK⟩
  let next : ℕ → Q → Q := fun j K =>
    (step _ ((isCompact_compactCovering U (j + 1)).union K.property)).choose
  let R : ℕ → Q := fun k => Nat.rec (step _ (isCompact_compactCovering U 0)).choose next k
  have hR0 : compactCovering U 0 ⊆ ((R 0).val : Set U) :=
    (step _ (isCompact_compactCovering U 0)).choose_spec
  have hRs : ∀ j, compactCovering U (j + 1) ∪ ((R j).val : Set U) ⊆ ((R (j + 1)).val : Set U) :=
    fun j => (step _ ((isCompact_compactCovering U (j + 1)).union (R j).property)).choose_spec
  have hcov : ∀ k, compactCovering U k ⊆ ((R k).val : Set U) := by
    intro k
    cases k with
    | zero => exact hR0
    | succ j => exact Set.subset_union_left.trans (hRs j)
  refine ⟨fun k => (R k).val, fun k => (R k).property, ?_, ?_⟩
  · refine monotone_nat_of_le_succ fun j => ?_
    intro g hg
    exact hRs j (Set.mem_union_right _ hg)
  · intro g
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ((iUnion_compactCovering U).symm ▸ Set.mem_univ g)
    exact ⟨k, hcov k hk⟩

/-- The rectangular matrices over `F` have a sequence of compact sets eventually containing
every compact set. -/
theorem exists_matrix_exhaustion (a b : ℕ) :
    letI := F.canonicalTopologicalData.topology
    ∃ E : ℕ → Set (Matrix (Fin a) (Fin b) F.Carrier), (∀ R, IsCompact (E R)) ∧
      ∀ C, IsCompact C → ∃ R, C ⊆ E R := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : SecondCountableTopology F.Carrier := T.secondCountableTopology
  have : LocallyCompactSpace (Matrix (Fin a) (Fin b) F.Carrier) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin b → F.Carrier))
  have : SecondCountableTopology (Matrix (Fin a) (Fin b) F.Carrier) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin b → F.Carrier))
  let E := CompactExhaustion.choice (Matrix (Fin a) (Fin b) F.Carrier)
  exact ⟨fun R => E R, E.isCompact, fun C hC => E.exists_superset_of_isCompact hC⟩

end Group

end Langlands.RankinSelberg.TwoBlockDeformation
