import Langlands.Representation.RankinSelberg.UniformFiniteFunctionMellinConvergenceProof
import Langlands.AllField.Representation.RankinSelberg.DeterminantSlicesSupplement
import Langlands.AllField.Representation.RankinSelberg.FiniteFunctionMellinProof
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatementSupplement
import Langlands.AllField.Representation.RankinSelberg.UniformFiniteFunctionMellinConvergenceStatement
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

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement FiniteFunctionMellinStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UniformFiniteFunctionMellinConvergenceStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def finiteFunctionMellin finiteFunctionShellSeries iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable uniformFiniteFunctionMellinConvergence zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory Filter
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open scoped BigOperators _root_.Topology

namespace UniformMellin
open Langlands.RankinSelberg.UniformMellin hiding exists_dilation uniformFiniteFunctionMellinConvergence_of_pointwise weight_mul
open Langlands.AllField.RankinSelberg.UniformMellin
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement FiniteFunctionMellinStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UniformFiniteFunctionMellinConvergenceStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def finiteFunctionMellin finiteFunctionShellSeries iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable uniformFiniteFunctionMellinConvergence zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

section Span


end Span

/-- A nonzero scalar dilation moves a compact set into a neighbourhood of zero. -/
theorem exists_dilation {F : Type*} [Field F] (T : LocalFieldData F)
    (r : ℕ) {K B : Set (Fin r → F)}
    (hK : letI := T.topology; IsCompact K)
    (hB : letI := T.topology; B ∈ 𝓝 (0 : Fin r → F)) :
    ∃ t : F, t ≠ 0 ∧ ∀ x ∈ K, t • x ∈ B := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hS : ∀ᶠ t in 𝓝 (0 : F), ∀ x ∈ K, t • x ∈ B := by
    apply hK.eventually_forall_of_forall_eventually
    intro x _
    have hc : Tendsto (fun z : F × (Fin r → F) => z.1 • z.2)
        (𝓝 (0, x)) (𝓝 0) := by
      simpa only [zero_smul] using
        (continuous_smul : Continuous fun z : F × (Fin r → F) =>
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
theorem weight_mul {F : Type*} [Field F] (T : LocalFieldData F)
    {r : ℕ} (m : Fin r → ℕ) (s : ℂ) (b a : Fin r → Fˣ) :
    ∏ i : Fin r, (T.normalizedAbs ((b * a) i : F) : ℂ) ^ ((m i : ℂ) * s) =
      (∏ i : Fin r, (T.normalizedAbs (b i : F) : ℂ) ^ ((m i : ℂ) * s)) *
        ∏ i : Fin r, (T.normalizedAbs (a i : F) : ℂ) ^ ((m i : ℂ) * s) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.mul_apply, Units.val_mul, T.normalizedAbs_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (T.normalizedAbs_nonneg _) (T.normalizedAbs_nonneg _)]

universe uF

/-- The uniform threshold follows from the pointwise finite-function Mellin theorem. -/
theorem uniformFiniteFunctionMellinConvergence_of_pointwise
    (hM : FiniteFunctionMellinStatement.{uF}) :
    UniformFiniteFunctionMellinConvergenceStatement.{uF} := by
  intro F _ T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel Fˣ
  let : BorelSpace Fˣ := ⟨rfl⟩
  let := T.fieldT2
  let := Langlands.AllField.RankinSelberg.MellinAssembly.field_totallyDisconnected F T
  let := Langlands.AllField.RankinSelberg.MellinAssembly.localHaar_sigmaFinite F T
  let := T.secondCountableTopology
  let : SecondCountableTopology Fˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  dsimp only
  intro r m hm X hX
  have hpw := hM F T r m hm
  dsimp only at hpw
  let dA : Measure (Fin r → Fˣ) :=
    Measure.pi fun _ : Fin r => localMultiplicativeHaar F
  let w : ℂ → (Fin r → Fˣ) → ℂ := fun s a =>
    ∏ i : Fin r, (T.normalizedAbs (a i : F) : ℂ) ^ ((m i : ℂ) * s)
  obtain ⟨B, hBc, hBo, hB0, -⟩ :=
    exists_compact_clopen (X := Fin r → F) (x := 0) (V := Set.univ) Filter.univ_mem
  let Φ₀ := clopenIndicator B hBc hBo
  have hone : ∀ η ∈ X, ∃ c : ℝ, ∀ s : ℂ, c < s.re →
      ∀ Φ : SchwartzBruhat (Fin r → F),
        Integrable (fun a => Φ (fun i => (a i : F)) * η a * w s a) dA := by
    intro η hη
    obtain ⟨hηc, hηf⟩ := hX η hη
    let e := Module.finBasis ℂ (translationSpan η)
    have hbasis : ∀ k, ∃ c : ℝ, ∀ s : ℂ, c < s.re →
        Integrable (fun a => Φ₀ (fun i => (a i : F)) * (e k : _ → ℂ) a * w s a) dA := by
      intro k
      have hk := finite_of_mem_translationSpan hηc hηf (e k).2
      have hXk : ∀ η' ∈ ({(e k : _ → ℂ)} : Finset ((Fin r → Fˣ) → ℂ)),
          Continuous η' ∧ FiniteDimensional ℂ (translationSpan η') := by
        intro η' hη'
        rw [Finset.mem_singleton] at hη'
        subst hη'
        exact hk
      have h1 := (hpw {(e k : _ → ℂ)} hXk).1
      have h2 := h1 _ (Finset.mem_singleton_self _) Φ₀
      exact h2
    obtain ⟨c, hc⟩ := MellinAssembly.uniform_right (fun k s => Integrable
      (fun a => Φ₀ (fun i => (a i : F)) * (e k : _ → ℂ) a * w s a) dA) hbasis
    refine ⟨c, fun s hs Φ => ?_⟩
    obtain ⟨t, ht, htK⟩ := exists_dilation T r Φ.hasCompactSupport.isCompact
      (hBo.isOpen.mem_nhds hB0)
    let b : Fin r → Fˣ := fun _ => (Units.mk0 t ht)⁻¹
    obtain ⟨C, hC⟩ := exists_translate_expansion e b
    obtain ⟨M, hMΦ⟩ := Φ.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
    have hΨc : Continuous fun a : Fin r → Fˣ => Φ (fun i => ((b * a) i : F)) :=
      Φ.continuous.comp (continuous_pi fun i => Units.continuous_val.comp
        ((continuous_apply i).comp (continuous_const.mul continuous_id)))
    refine integrable_of_translate_expansion dA _ _ _ (fun k => C k * w s b) b M
      (fun k => hc s hs k) hΨc.aestronglyMeasurable (fun a => hMΦ _) fun a => ?_
    have hsupp : Φ (fun i => ((b * a) i : F)) =
        Φ (fun i => ((b * a) i : F)) * Φ₀ (fun i => (a i : F)) := by
      by_cases h0 : Φ (fun i => ((b * a) i : F)) = 0
      · rw [h0, zero_mul]
      have hmem := htK _ (subset_tsupport _ h0)
      have hta : (t • fun i => ((b * a) i : F)) = fun i => (a i : F) := by
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
      SchwartzBruhat (Fin r → F),
        Integrable (fun a => Φ (fun i => (a i : F)) * (η : _ → ℂ) a * w s a) dA)
    fun η => hone η.1 η.2
  exact ⟨c, fun η hη Φ s hs => hc s hs ⟨η, hη⟩ Φ⟩

end UniformMellin

universe uF

/-- One right half-plane of convergence works for a whole finite family of
finite functions and every Schwartz--Bruhat test function. -/
theorem uniformFiniteFunctionMellinConvergence :
    UniformFiniteFunctionMellinConvergenceStatement.{uF} :=
  Langlands.AllField.RankinSelberg.UniformMellin.uniformFiniteFunctionMellinConvergence_of_pointwise finiteFunctionMellin.{uF}

end Langlands.AllField.RankinSelberg
