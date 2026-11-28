import Langlands.Global.ArthurTruncationL2Statement
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.UrysohnsLemma

/-! # A criterion for an orthogonal projection extension on `L²`

Let `X` be a locally compact, σ-compact Hausdorff space with a regular Borel measure. A pointwise
operator `Λ` on complex functions that preserves measurable functions bounded on compact sets,
is idempotent on continuous compactly supported functions, and is symmetric for the pairing of
such a function with a continuous compactly supported test function, admits an orthogonal
projection on `L²` agreeing almost everywhere with `Λ` on every square-integrable measurable
function bounded on compact sets. -/

noncomputable section

open MeasureTheory Set Filter Topology ComplexConjugate
open scoped ENNReal InnerProductSpace

namespace Langlands.Global.ArthurTruncation

section Criterion

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] {m : Measure X} [m.Regular]

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- The product of a function bounded on compact sets with a continuous compactly supported
function is integrable. -/
theorem integrable_mul_of_isCompact_bound {g ψ : X → ℂ} (hg : AEStronglyMeasurable g m)
    (hb : ∀ C : Set X, IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖g x‖ ≤ M)
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun x => g x * ψ x) m := by
  obtain ⟨M, hM⟩ := hb _ hψc
  obtain ⟨N, hN⟩ := hψc.exists_bound_of_continuousOn hψ.continuousOn
  have hsupp : Function.support (fun x => g x * ψ x) ⊆ tsupport ψ :=
    fun x hx => subset_tsupport _ (right_ne_zero_of_mul hx)
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  refine Measure.integrableOn_of_bounded (M := M * N) hψc.measure_lt_top.ne
    (hg.mul hψ.aestronglyMeasurable) ?_
  rw [ae_restrict_iff' (isClosed_tsupport ψ).measurableSet]
  refine ae_of_all _ fun x hx => ?_
  rw [norm_mul]
  exact mul_le_mul (hM x hx) (hN x hx) (norm_nonneg _) ((norm_nonneg _).trans (hM x hx))

omit [BorelSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- A function bounded on compact sets and supported in a compact set is square integrable. -/
theorem memLp_two_of_isCompact_bound {g : X → ℂ} (hg : AEStronglyMeasurable g m)
    {K : Set X} (hK : IsCompact K) (hgK : ∀ x, x ∉ K → g x = 0) {M : ℝ}
    (hM : ∀ x ∈ K, ‖g x‖ ≤ M) : MemLp g 2 m := by
  have htop : MemLp g ∞ m := by
    refine memLp_top_of_bound hg (max M 0) (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ K
    · exact (hM x hx).trans (le_max_left _ _)
    · rw [hgK x hx, norm_zero]
      exact le_max_right _ _
  exact htop.mono_exponent_of_measure_support_ne_top hgK hK.measure_lt_top.ne le_top

variable (m) in
/-- Continuous compactly supported classes are dense in `L²`. -/
theorem dense_compactSupport_toLp :
    Dense {Ψ : Lp ℂ 2 m | ∃ (ψ : X → ℂ) (hψ : MemLp ψ 2 m),
      Continuous ψ ∧ HasCompactSupport ψ ∧ hψ.toLp ψ = Ψ} := by
  rw [Metric.dense_iff]
  intro U ε hε
  obtain ⟨ψ, hψc, hle, hψ, hψm⟩ := (Lp.memLp U).exists_hasCompactSupport_eLpNorm_sub_le
    ENNReal.ofNat_ne_top (ε := ENNReal.ofReal (ε / 2)) (by simpa using half_pos hε)
  refine ⟨hψm.toLp ψ, ?_, ⟨ψ, hψm, hψ, hψc, rfl⟩⟩
  rw [Metric.mem_ball, Lp.dist_def]
  have heq : eLpNorm (⇑(hψm.toLp ψ) - ⇑U) 2 m = eLpNorm (⇑U - ψ) 2 m := by
    rw [← eLpNorm_neg]
    apply eLpNorm_congr_ae
    filter_upwards [hψm.coeFn_toLp] with x hx
    simp [hx]
  rw [heq]
  calc (eLpNorm (⇑U - ψ) 2 m).toReal ≤ ε / 2 :=
        ENNReal.toReal_le_of_le_ofReal (half_pos hε).le hle
    _ < ε := half_lt_self hε

/-- A square-integrable function orthogonal to every continuous compactly supported function
vanishes almost everywhere. -/
theorem ae_eq_zero_of_forall_integral_mul_conj {u : X → ℂ} (hu : MemLp u 2 m)
    (h : ∀ ψ : X → ℂ, Continuous ψ → HasCompactSupport ψ → ∫ x, u x * conj (ψ x) ∂m = 0) :
    u =ᵐ[m] 0 := by
  have hU : hu.toLp u = 0 := by
    apply (dense_compactSupport_toLp m).eq_zero_of_inner_right ℂ
    rintro _ ⟨ψ, hψm, hψ, hψc, rfl⟩
    rw [L2.inner_def]
    calc ∫ x, ⟪(hψm.toLp ψ) x, (hu.toLp u) x⟫_ℂ ∂m = ∫ x, u x * conj (ψ x) ∂m := by
          apply integral_congr_ae
          filter_upwards [hψm.coeFn_toLp, hu.coeFn_toLp] with x h1 h2
          rw [h1, h2, RCLike.inner_apply]
      _ = 0 := h ψ hψ hψc
  have h1 := hu.coeFn_toLp
  rw [hU] at h1
  filter_upwards [h1, Lp.coeFn_zero ℂ 2 m] with x hx hx0
  rw [← hx, hx0]

/-- The local form: a function bounded on compact sets and a square-integrable function with the
same pairings against every continuous compactly supported function agree almost everywhere. -/
theorem ae_eq_of_forall_integral_mul_conj [SigmaCompactSpace X] {g₁ g₂ : X → ℂ}
    (hg₁ : AEStronglyMeasurable g₁ m) (hb₁ : ∀ C : Set X, IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖g₁ x‖ ≤ M)
    (hg₂ : MemLp g₂ 2 m)
    (h : ∀ ψ : X → ℂ, Continuous ψ → HasCompactSupport ψ →
      ∫ x, g₁ x * conj (ψ x) ∂m = ∫ x, g₂ x * conj (ψ x) ∂m) :
    g₁ =ᵐ[m] g₂ := by
  have hloc : ∀ s : Set X, IsCompact s → ∀ᵐ x ∂(m.restrict s), g₁ x = g₂ x := by
    intro s hs
    obtain ⟨η, hη1, -, hηc, hη01⟩ :=
      exists_continuous_one_zero_of_isCompact hs isClosed_empty (Set.disjoint_empty s)
    let ηC : X → ℂ := fun x => ((η x : ℝ) : ℂ)
    have hηC : Continuous ηC := Complex.continuous_ofReal.comp η.continuous
    have hηCc : HasCompactSupport ηC := hηc.comp_left Complex.ofReal_zero
    let u : X → ℂ := fun x => ηC x * (g₁ x - g₂ x)
    have hηtop : MemLp ηC ∞ m := hηC.memLp_top_of_hasCompactSupport hηCc m
    have hu₂ : MemLp (fun x => ηC x * g₂ x) 2 m := hηtop.mul hg₂
    obtain ⟨M, hM⟩ := hb₁ _ hηCc
    have hu₁ : MemLp (fun x => ηC x * g₁ x) 2 m := by
      refine memLp_two_of_isCompact_bound (hηC.aestronglyMeasurable.mul hg₁) hηCc
        (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]) (M := M) ?_
      intro x hx
      rw [norm_mul]
      have : ‖ηC x‖ ≤ 1 := by
        simp only [ηC, Complex.norm_real, Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [(hη01 x).1], (hη01 x).2⟩
      calc ‖ηC x‖ * ‖g₁ x‖ ≤ 1 * ‖g₁ x‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ ≤ M := by rw [one_mul]; exact hM x hx
    have hu : MemLp u 2 m := by
      have := hu₁.sub hu₂
      convert this using 1
      funext x
      simp only [u, Pi.sub_apply, mul_sub]
    have horth : ∀ ψ : X → ℂ, Continuous ψ → HasCompactSupport ψ →
        ∫ x, u x * conj (ψ x) ∂m = 0 := by
      intro ψ hψ hψc
      let φ : X → ℂ := fun x => ηC x * ψ x
      have hφ : Continuous φ := hηC.mul hψ
      have hφc : HasCompactSupport φ := hψc.mul_left
      have hφ' : Continuous (fun x => conj (φ x)) := Complex.continuous_conj.comp hφ
      have hφc' : HasCompactSupport (fun x => conj (φ x)) := hφc.comp_left (map_zero _)
      have hi₁ : Integrable (fun x => g₁ x * conj (φ x)) m :=
        integrable_mul_of_isCompact_bound hg₁ hb₁ hφ' hφc'
      have hi₂ : Integrable (fun x => g₂ x * conj (φ x)) m :=
        hg₂.integrable_mul (q := 2) (hφ'.memLp_of_hasCompactSupport hφc')
      have hpt : (fun x => u x * conj (ψ x)) =
          fun x => g₁ x * conj (φ x) - g₂ x * conj (φ x) := by
        funext x
        simp only [u, φ, ηC, map_mul, Complex.conj_ofReal]
        ring
      rw [hpt, integral_sub hi₁ hi₂, h φ hφ hφc, sub_self]
    have hu0 := ae_eq_zero_of_forall_integral_mul_conj hu horth
    rw [ae_restrict_iff' hs.measurableSet]
    filter_upwards [hu0] with x hx hxs
    have h1 : ηC x = 1 := by simp [ηC, hη1 hxs]
    have : u x = 0 := hx
    simp only [u, h1, one_mul] at this
    exact sub_eq_zero.mp this
  have hall : ∀ᵐ x ∂(m.restrict (⋃ n, compactCovering X n)), g₁ x = g₂ x :=
    (ae_restrict_iUnion_iff _ _).2 fun n => hloc _ (isCompact_compactCovering X n)
  rwa [iUnion_compactCovering, Measure.restrict_univ] at hall

/-- **Orthogonal projection criterion.** Let `Λ` preserve measurable functions bounded on compact
sets, be idempotent on continuous compactly supported functions, and satisfy
`∫ (Λ f) ψ̄ = ∫ f (Λ ψ)‾`, with the right side integrable, for every measurable `f` bounded on
compact sets and every continuous compactly supported `ψ`. Then `Λ` has an orthogonal projection
extension on `L²(X, m)`: the projection onto the orthogonal complement of the classes
`ψ - Λ ψ`. -/
theorem isOrthogonalL2Extension_of_pairing (Λ : (X → ℂ) → X → ℂ)
    (hloc : ∀ f : X → ℂ, Measurable f →
      (∀ C : Set X, IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖f x‖ ≤ M) →
      Measurable (Λ f) ∧ ∀ C : Set X, IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖Λ f x‖ ≤ M)
    (hidem : ∀ ψ : X → ℂ, Continuous ψ → HasCompactSupport ψ → Λ (Λ ψ) = Λ ψ)
    (hpair : ∀ f ψ : X → ℂ, Measurable f →
      (∀ C : Set X, IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖f x‖ ≤ M) →
      Continuous ψ → HasCompactSupport ψ →
      Integrable (fun x => f x * conj (Λ ψ x)) m ∧
        ∫ x, Λ f x * conj (ψ x) ∂m = ∫ x, f x * conj (Λ ψ x) ∂m) :
    IsOrthogonalL2Extension m Λ := by
  classical
  have hcb : ∀ ψ : X → ℂ, Continuous ψ →
      ∀ C : Set X, IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖ψ x‖ ≤ M :=
    fun ψ hψ C hC => hC.exists_bound_of_continuousOn hψ.continuousOn
  have hΛmem : ∀ ψ : X → ℂ, Continuous ψ → HasCompactSupport ψ → MemLp (Λ ψ) 2 m := by
    intro ψ hψ hψc
    obtain ⟨hm, hb⟩ := hloc ψ hψ.measurable (hcb ψ hψ)
    obtain ⟨hint, -⟩ := hpair (Λ ψ) ψ hm hb hψ hψc
    rw [memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable]
    refine hint.norm.congr (ae_of_all _ fun x => ?_)
    simp only [norm_mul, Complex.norm_conj, sq]
  let c : {ψ : X → ℂ // Continuous ψ ∧ HasCompactSupport ψ} → Lp ℂ 2 m :=
    fun ψ => (ψ.2.1.memLp_of_hasCompactSupport ψ.2.2).toLp ψ.1
  let v : {ψ : X → ℂ // Continuous ψ ∧ HasCompactSupport ψ} → Lp ℂ 2 m :=
    fun ψ => (hΛmem ψ.1 ψ.2.1 ψ.2.2).toLp (Λ ψ.1)
  let S : Submodule ℂ (Lp ℂ 2 m) := Submodule.span ℂ (Set.range fun ψ => c ψ - v ψ)
  refine ⟨Sᗮ.starProjection, isStarProjection_starProjection, ?_⟩
  have hinner : ∀ (f g : X → ℂ) (hf : MemLp f 2 m) (hg : MemLp g 2 m),
      ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ x, g x * conj (f x) ∂m := by
    intro f g hf hg
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2, RCLike.inner_apply]
  have hsym : ∀ ψ χ : {ψ : X → ℂ // Continuous ψ ∧ HasCompactSupport ψ},
      ∫ x, Λ ψ.1 x * conj (χ.1 x) ∂m = ∫ x, Λ ψ.1 x * conj (Λ χ.1 x) ∂m := by
    intro ψ χ
    obtain ⟨hm, hb⟩ := hloc ψ.1 ψ.2.1.measurable (hcb ψ.1 ψ.2.1)
    have := (hpair (Λ ψ.1) χ.1 hm hb χ.2.1 χ.2.2).2
    rwa [hidem ψ.1 ψ.2.1 ψ.2.2] at this
  have hvW : ∀ ψ, v ψ ∈ Sᗮ := by
    intro ψ
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨χ, rfl⟩ := hu
      rw [inner_sub_left, hinner, hinner, sub_eq_zero]
      exact hsym ψ χ
    | zero => simp
    | add u w _ _ hu hw => rw [inner_add_left, hu, hw, add_zero]
    | smul a u _ hu => rw [inner_smul_left, hu, mul_zero]
  have hPc : ∀ ψ, Sᗮ.starProjection (c ψ) = v ψ := by
    intro ψ
    refine Submodule.eq_starProjection_of_mem_orthogonal' (hvW ψ)
      (Submodule.le_orthogonal_orthogonal S (Submodule.subset_span ⟨ψ, rfl⟩)) ?_
    rw [add_sub_cancel]
  intro f hf hfm hfb
  obtain ⟨hΛm, hΛb⟩ := hloc f hfm hfb
  symm
  refine ae_eq_of_forall_integral_mul_conj hΛm.aestronglyMeasurable hΛb (Lp.memLp _) ?_
  intro ψ hψ hψc
  let ψ' : {ψ : X → ℂ // Continuous ψ ∧ HasCompactSupport ψ} := ⟨ψ, hψ, hψc⟩
  have h1 : ∫ x, (Sᗮ.starProjection (hf.toLp f)) x * conj (ψ x) ∂m =
      ⟪c ψ', Sᗮ.starProjection (hf.toLp f)⟫_ℂ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hψ.memLp_of_hasCompactSupport (μ := m) (p := 2) hψc).coeFn_toLp] with x hx
    change _ = ⟪(c ψ') x, _⟫_ℂ
    rw [show (c ψ') x = ψ x from hx, RCLike.inner_apply]
  rw [h1, ← Submodule.inner_starProjection_left_eq_right, hPc ψ', hinner,
    (hpair f ψ hfm hfb hψ hψc).2]

end Criterion

end Langlands.Global.ArthurTruncation
