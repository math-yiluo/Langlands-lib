import Langlands.Representation.RankinSelberg.UniformFiniteFunctionMellinConvergenceStatement
import Langlands.Representation.RankinSelberg.FiniteFunctionMellinProof
import Langlands.HarmonicAnalysis.SchwartzBruhatValuationBoundsProof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

/-!
# A test-independent Mellin convergence threshold: proof

A finite basis of the translation span of a finite function receives one
convergence threshold from the published pointwise theorem, applied to the
indicator of a fixed compact clopen box. An arbitrary test is moved into that
box by a scalar dilation; left invariance of the product multiplicative Haar
measure and the finite basis expansion of the dilated function reduce its
integrand to bounded multiples of the fixed basis integrands.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Filter
open scoped BigOperators Topology

namespace UniformMellin

section Span

variable {G : Type*} [Monoid G]

/-- The complex span of the left translates of a function. -/
abbrev translationSpan (η : G → ℂ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (Set.range fun b : G => fun a : G => η (b * a))

theorem translate_mem_translationSpan (η : G → ℂ) (b : G) {g : G → ℂ}
    (hg : g ∈ translationSpan η) : (fun a => g (b * a)) ∈ translationSpan η := by
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, rfl⟩ := hy
    exact Submodule.subset_span ⟨c * b, funext fun a => by simp only [mul_assoc]⟩
  | zero => exact (translationSpan η).zero_mem
  | add y z _ _ hy hz => exact (translationSpan η).add_mem hy hz
  | smul c y _ hy => exact (translationSpan η).smul_mem c hy

theorem translationSpan_le (η : G → ℂ) {g : G → ℂ} (hg : g ∈ translationSpan η) :
    translationSpan g ≤ translationSpan η :=
  Submodule.span_le.mpr (by
    rintro _ ⟨b, rfl⟩
    exact translate_mem_translationSpan η b hg)

theorem continuous_of_mem_translationSpan [TopologicalSpace G] [ContinuousMul G]
    {η : G → ℂ} (hη : Continuous η) {g : G → ℂ} (hg : g ∈ translationSpan η) :
    Continuous g := by
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, rfl⟩ := hy
    exact hη.comp (continuous_const.mul continuous_id)
  | zero => exact continuous_const
  | add y z _ _ hy hz => exact hy.add hz
  | smul c y _ hy => exact hy.const_smul c

/-- Every member of the translation span of a finite function is a finite function. -/
theorem finite_of_mem_translationSpan [TopologicalSpace G] [ContinuousMul G]
    {η : G → ℂ} (hη : Continuous η) (hfin : FiniteDimensional ℂ (translationSpan η))
    {g : G → ℂ} (hg : g ∈ translationSpan η) :
    Continuous g ∧ FiniteDimensional ℂ (translationSpan g) :=
  ⟨continuous_of_mem_translationSpan hη hg,
    Submodule.finiteDimensional_of_le (translationSpan_le η hg)⟩

/-- Each translate of `η` is a combination of a chosen basis of its translation span. -/
theorem exists_translate_expansion {η : G → ℂ} {d : ℕ}
    (e : Module.Basis (Fin d) ℂ (translationSpan η)) (b : G) :
    ∃ c : Fin d → ℂ, ∀ a, η (b * a) = ∑ k, c k * (e k : G → ℂ) a := by
  have hmem : (fun a => η (b * a)) ∈ translationSpan η := Submodule.subset_span ⟨b, rfl⟩
  refine ⟨fun k => e.repr ⟨_, hmem⟩ k, fun a => ?_⟩
  have h := congrArg (fun v : translationSpan η => (v : G → ℂ) a) (e.sum_repr ⟨_, hmem⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  exact h.symm

end Span

/-- Integrability is recovered from a left translate written as a finite sum of
bounded multiples of integrable functions. -/
theorem integrable_of_translate_expansion {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] {ι : Type*} [Fintype ι]
    (f Ψ : G → ℂ) (h : ι → G → ℂ) (C : ι → ℂ) (b : G) (M : ℝ)
    (hh : ∀ k, Integrable (h k) μ) (hΨ : AEStronglyMeasurable Ψ μ) (hΨM : ∀ a, ‖Ψ a‖ ≤ M)
    (hf : ∀ a, f (b * a) = ∑ k, C k * (Ψ a * h k a)) :
    Integrable f μ := by
  have h1 : Integrable (fun a => f (b * a)) μ := by
    simp_rw [hf]
    exact integrable_finsetSum _ fun k _ =>
      ((hh k).bdd_mul hΨ (Eventually.of_forall hΨM)).const_mul (C k)
  simpa only [mul_inv_cancel_left] using h1.comp_mul_left b⁻¹

/-- The indicator of a compact clopen set, as a Schwartz--Bruhat function. -/
def clopenIndicator {X : Type*} [TopologicalSpace X] [T2Space X] (U : Set X)
    (hUc : IsCompact U) (hUo : IsClopen U) : SchwartzBruhat X :=
  ⟨U.indicator (fun _ => 1),
    ((LocallyConstant.const X (1 : ℂ)).indicator hUo).isLocallyConstant,
    HasCompactSupport.intro hUc (fun _ hx => Set.indicator_of_notMem hx _)⟩

theorem clopenIndicator_apply_of_mem {X : Type*} [TopologicalSpace X] [T2Space X]
    {U : Set X} (hUc : IsCompact U) (hUo : IsClopen U) {x : X} (hx : x ∈ U) :
    clopenIndicator U hUc hUo x = 1 := by
  change U.indicator (fun _ => (1 : ℂ)) x = 1
  exact Set.indicator_of_mem hx _

/-- A nonzero scalar dilation moves a compact set into a neighbourhood of zero. -/
theorem exists_dilation {p : ℕ} [Fact p.Prime] {F : PadicField p} (T : F.TopologicalData)
    (r : ℕ) {K B : Set (Fin r → F.Carrier)}
    (hK : letI := T.topology; IsCompact K)
    (hB : letI := T.topology; B ∈ 𝓝 (0 : Fin r → F.Carrier)) :
    ∃ t : F.Carrier, t ≠ 0 ∧ ∀ x ∈ K, t • x ∈ B := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hS : ∀ᶠ t in 𝓝 (0 : F.Carrier), ∀ x ∈ K, t • x ∈ B := by
    apply hK.eventually_forall_of_forall_eventually
    intro x _
    have hc : Tendsto (fun z : F.Carrier × (Fin r → F.Carrier) => z.1 • z.2)
        (𝓝 (0, x)) (𝓝 0) := by
      simpa only [zero_smul] using
        (continuous_smul : Continuous fun z : F.Carrier × (Fin r → F.Carrier) =>
          z.1 • z.2).tendsto (0, x)
    exact hc hB
  obtain ⟨ε, hε, hball⟩ := T.exists_normalizedAbs_ball_subset hS
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hq)
  obtain ⟨t, ht, hord⟩ := T.ord_surjective_nonzero N
  refine ⟨t, ht, hball t ?_⟩
  rw [T.normalizedAbs_of_ne_zero ht, hord, zpow_neg, zpow_natCast, ← inv_pow]
  exact hN

/-- The normalized absolute-value weight is multiplicative on the torus. -/
theorem weight_mul {p : ℕ} [Fact p.Prime] {F : PadicField p} (T : F.TopologicalData)
    {r : ℕ} (m : Fin r → ℕ) (s : ℂ) (b a : Fin r → F.Carrierˣ) :
    ∏ i : Fin r, (T.normalizedAbs ((b * a) i : F.Carrier) : ℂ) ^ ((m i : ℂ) * s) =
      (∏ i : Fin r, (T.normalizedAbs (b i : F.Carrier) : ℂ) ^ ((m i : ℂ) * s)) *
        ∏ i : Fin r, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((m i : ℂ) * s) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.mul_apply, Units.val_mul, T.normalizedAbs_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (T.normalizedAbs_nonneg _) (T.normalizedAbs_nonneg _)]

universe uF

/-- The uniform threshold follows from the pointwise finite-function Mellin theorem. -/
theorem uniformFiniteFunctionMellinConvergence_of_pointwise
    (hM : FiniteFunctionMellinStatement.{uF}) :
    UniformFiniteFunctionMellinConvergenceStatement.{uF} := by
  intro p hp F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let := T.fieldT2
  let := MellinAssembly.field_totallyDisconnected F T
  let := MellinAssembly.localHaar_sigmaFinite F T
  let := T.secondCountableTopology
  let : SecondCountableTopology F.Carrierˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  dsimp only
  intro r m hm X hX
  have hpw := hM p hp F T r m hm
  dsimp only at hpw
  let dA : Measure (Fin r → F.Carrierˣ) :=
    Measure.pi fun _ : Fin r => localMultiplicativeHaar F.Carrier
  let w : ℂ → (Fin r → F.Carrierˣ) → ℂ := fun s a =>
    ∏ i : Fin r, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((m i : ℂ) * s)
  obtain ⟨B, hBc, hBo, hB0, -⟩ :=
    exists_compact_clopen (X := Fin r → F.Carrier) (x := 0) (V := Set.univ) Filter.univ_mem
  let Φ₀ := clopenIndicator B hBc hBo
  have hone : ∀ η ∈ X, ∃ c : ℝ, ∀ s : ℂ, c < s.re →
      ∀ Φ : SchwartzBruhat (Fin r → F.Carrier),
        Integrable (fun a => Φ (fun i => (a i : F.Carrier)) * η a * w s a) dA := by
    intro η hη
    obtain ⟨hηc, hηf⟩ := hX η hη
    let e := Module.finBasis ℂ (translationSpan η)
    have hbasis : ∀ k, ∃ c : ℝ, ∀ s : ℂ, c < s.re →
        Integrable (fun a => Φ₀ (fun i => (a i : F.Carrier)) * (e k : _ → ℂ) a * w s a) dA := by
      intro k
      have hk := finite_of_mem_translationSpan hηc hηf (e k).2
      have hXk : ∀ η' ∈ ({(e k : _ → ℂ)} : Finset ((Fin r → F.Carrierˣ) → ℂ)),
          Continuous η' ∧ FiniteDimensional ℂ (translationSpan η') := by
        intro η' hη'
        rw [Finset.mem_singleton] at hη'
        subst hη'
        exact hk
      have h1 := (hpw {(e k : _ → ℂ)} hXk).1
      have h2 := h1 _ (Finset.mem_singleton_self _) Φ₀
      exact h2
    obtain ⟨c, hc⟩ := MellinAssembly.uniform_right (fun k s => Integrable
      (fun a => Φ₀ (fun i => (a i : F.Carrier)) * (e k : _ → ℂ) a * w s a) dA) hbasis
    refine ⟨c, fun s hs Φ => ?_⟩
    obtain ⟨t, ht, htK⟩ := exists_dilation T r Φ.hasCompactSupport.isCompact
      (hBo.isOpen.mem_nhds hB0)
    let b : Fin r → F.Carrierˣ := fun _ => (Units.mk0 t ht)⁻¹
    obtain ⟨C, hC⟩ := exists_translate_expansion e b
    obtain ⟨M, hMΦ⟩ := Φ.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
    have hΨc : Continuous fun a : Fin r → F.Carrierˣ => Φ (fun i => ((b * a) i : F.Carrier)) :=
      Φ.continuous.comp (continuous_pi fun i => Units.continuous_val.comp
        ((continuous_apply i).comp (continuous_const.mul continuous_id)))
    refine integrable_of_translate_expansion dA _ _ _ (fun k => C k * w s b) b M
      (fun k => hc s hs k) hΨc.aestronglyMeasurable (fun a => hMΦ _) fun a => ?_
    have hsupp : Φ (fun i => ((b * a) i : F.Carrier)) =
        Φ (fun i => ((b * a) i : F.Carrier)) * Φ₀ (fun i => (a i : F.Carrier)) := by
      by_cases h0 : Φ (fun i => ((b * a) i : F.Carrier)) = 0
      · rw [h0, zero_mul]
      have hmem := htK _ (subset_tsupport _ h0)
      have hta : (t • fun i => ((b * a) i : F.Carrier)) = fun i => (a i : F.Carrier) := by
        funext i
        simp [b, Pi.mul_apply, Units.val_mul, ← mul_assoc, mul_inv_cancel₀ ht]
      rw [hta] at hmem
      rw [clopenIndicator_apply_of_mem hBc hBo hmem, mul_one]
    simp only [w] at hC ⊢
    rw [weight_mul]
    conv_lhs => rw [hsupp]
    rw [hC, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  obtain ⟨c, hc⟩ := MellinAssembly.uniform_right (fun (η : X) s => ∀ Φ :
      SchwartzBruhat (Fin r → F.Carrier),
        Integrable (fun a => Φ (fun i => (a i : F.Carrier)) * (η : _ → ℂ) a * w s a) dA)
    fun η => hone η.1 η.2
  exact ⟨c, fun η hη Φ s hs => hc s hs ⟨η, hη⟩ Φ⟩

end UniformMellin

universe uF

/-- One right half-plane of convergence works for a whole finite family of
finite functions and every Schwartz--Bruhat test function. -/
theorem uniformFiniteFunctionMellinConvergence :
    UniformFiniteFunctionMellinConvergenceStatement.{uF} :=
  UniformMellin.uniformFiniteFunctionMellinConvergence_of_pointwise finiteFunctionMellin.{uF}

end Langlands.RankinSelberg
