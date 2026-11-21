import Langlands.GroupScheme.Rational.SemistandardSpectralDynamicCoverageProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CompatibleCentralQuotientVolumeBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientConvergence
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedConstantTermFourier
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedTemperedCoefficients
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierTransform
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWavePacket

/-! # Absolute convergence of the Fourier pairing from constant-term estimates -/

noncomputable section

universe uG uV

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel
open scoped ComplexConjugate ENNReal NNReal Pointwise TensorProduct

namespace Langlands.HarishChandraSchwartz

section Translates

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Nonempty (CompactOpenSubgroup G)] {Ξ σ : G → ℝ}

/-- A fixed Schwartz function has only finitely many double translates over a
compact subgroup. Their finite seminorms admit one upper bound. -/
private theorem exists_uniform_compact_translate_nu (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (ht : TranslationWeights Ξ σ) (f : Space Ξ σ) (d : ℝ) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ k ∈ K, ∀ l ∈ K, nu Ξ σ d (Space.translate ht k l f) ≤ B := by
  classical
  obtain ⟨H, hH⟩ := Space.exists_isBiInvariant f
  obtain ⟨T, hT⟩ := Langlands.QuotientIntegration.exists_finset_leftCoset_cover H.1 hK
  let N (a b : G) := nu Ξ σ d (Space.translate ht a b f)
  refine ⟨∑ a ∈ T, ∑ b ∈ T, N a b, ?_, ?_⟩
  · refine ENNReal.sum_lt_top.mpr fun a _ => ENNReal.sum_lt_top.mpr fun b _ => ?_
    obtain ⟨Q, hQ⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp
      (Space.coe_mem (Space.translate ht a b f))
    exact hQ.2 d
  · intro k hk l hl
    obtain ⟨a, hka⟩ := Set.mem_iUnion.mp (hT hk)
    obtain ⟨ha, hka⟩ := Set.mem_iUnion.mp hka
    obtain ⟨b, hlb⟩ := Set.mem_iUnion.mp (hT hl)
    obtain ⟨hb, hlb⟩ := Set.mem_iUnion.mp hlb
    obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.mp hka
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hlb
    have he : Space.translate ht (a * x) (b * y) f = Space.translate ht a b f := by
      apply Space.ext
      intro g
      simp only [Space.translate_apply, mul_inv_rev]
      have key : y⁻¹ * b⁻¹ * g * (a * x) = y⁻¹ * (b⁻¹ * g * a) * x := by group
      rw [key, hH _ (H.toSubgroup.inv_mem hy) _ hx]
    change nu Ξ σ d (Space.translate ht (a * x) (b * y) f) ≤ _
    rw [he]
    exact (Finset.single_le_sum (f := N a) (fun _ _ => zero_le) hb).trans
      (Finset.single_le_sum (f := fun a => ∑ b ∈ T, N a b) (fun _ _ => zero_le) ha)

end Translates

section Convergence

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  {mu : Measure G} [SFinite mu] [mu.IsMulLeftInvariant]
  {muM : Measure M} [SFinite muM] [muM.IsMulLeftInvariant]
  {muU : Measure U} [SFinite muU] [muU.IsMulLeftInvariant]
  {Ξ σ : G → ℝ} {ΞM σM : M → ℝ}

set_option hygiene false in
local notation "δ" => HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer

/-- The actual VII.1.2 double integral is absolutely convergent under
normalized Iwasawa integration, the constant-term estimate and tempered
Levi coefficients. -/
def ConstantTermFourierDoubleIntegrabilityStatement : Prop :=
  IsUnimodularModulus U hU →
  (∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k) →
  (∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K) →
  mu (K : Set G) = 1 → muM {m : M | (m : G) ∈ K} = 1 → muU {u : U | (u : G) ∈ K} = 1 →
  ConstantTermEstimate muU δ Ξ σ ΞM σM → TranslationWeights Ξ σ → L2Weights muM ΞM σM →
  HasTemperedCoefficients ΞM σM A.representation →
  ∀ (ψ : productInducedCoefficientObject h hU A) (f : Space Ξ σ),
    Integrable (coefficientPairingIntegrand h hU A K ψ f) (mu.prod (CompactInduction.measure K hK))

set_option maxHeartbeats 3000000 in
/-- In the Iwasawa integral the square root of the modulus belongs to the
absolute constant-term estimate. The remaining Levi integral is the square
weight, with a Schwartz seminorm bound uniform over the compact translates. -/
theorem constantTermFourierDoubleIntegrability :
    ConstantTermFourierDoubleIntegrabilityStatement h hU A K hK
      (mu := mu) (muM := muM) (muU := muU) (Ξ := Ξ) (σ := σ) (ΞM := ΞM) (σM := σM) := by
  intro hδU hPK hsplit hμK hMK hUK hE ht hwM hT ψ f
  let : Nonempty (CompactOpenSubgroup G) := ⟨⟨K, hK⟩⟩
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  let : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology _
  have hfac (g : G) : ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k := by
    obtain ⟨q, hq, k, hk, rfl⟩ := hPK g
    exact ⟨h.projection ⟨q, hq⟩, ⟨_, h.projection_inv_mul_mem ⟨q, hq⟩⟩, k, hk, by simp⟩
  obtain ⟨C, R, hC, _, hc⟩ := exists_coefficientTensorMap_le_rpow A (fun m => (hwM.pos m).le)
    hwM.nonneg hT (Set.range (CompactInduction.compactValue h hU A K ψ))
    (CompactInduction.compactValue_range_finite h hU A K hK ψ)
  let r := hwM.exponent + R
  obtain ⟨s, c, hct⟩ := hE r
  obtain ⟨B, hB, htr⟩ := exists_uniform_compact_translate_nu K hK ht f s
  let J := coefficientPairingIntegrand h hU A K ψ f
  have hJ : Continuous J := (Complex.continuous_conj.comp
    (continuous_integrand_uncurry h hU A K ψ)).mul ((Space.continuous f).comp continuous_fst)
  let L (m : M) := ENNReal.ofReal (C * (ΞM m * (1 + σM m) ^ R))
  let W (m : M) (u : U) := ENNReal.ofReal (Ξ ((m : G) * u) * (1 + σ ((m : G) * u)) ^ (-s))
  let D (m : M) : ℝ≥0∞ := NNReal.sqrt (δ m)
  let E (m : M) := ENNReal.ofReal (ΞM m ^ 2 * (1 + σM m) ^ (-hwM.exponent))
  let T := ENNReal.ofReal C * B * (c : ℝ≥0∞)
  have hTfin : T ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB.ne)
    ENNReal.coe_ne_top
  have hslice (l : K) (k : G) (hk : k ∈ K) (m : M) :
      ∫⁻ u : U, ‖J ((l : G)⁻¹ * ((m : G) * u * k), l)‖ₑ ∂muU ≤ T * E m := by
    have hpt (u : U) : ‖J ((l : G)⁻¹ * ((m : G) * u * k), l)‖ₑ ≤
        (L m * B * D m) * W m u := by
      have hf := enorm_le_nu_mul ht.pos ht.nonneg (Space.translate ht k l f) s ((m : G) * u)
      rw [Space.translate_apply, mul_assoc (l : G)⁻¹] at hf
      have hf' := hf.trans (mul_le_mul_of_nonneg_right (htr k hk l l.property) zero_le)
      let t := CompactInduction.compactValue h hU A K ψ (⟨k, hk⟩, l)
      have hcoeff : ‖coefficientTensorMap A t m‖ₑ ≤ L m := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hc t ⟨_, rfl⟩ m)
      rw [show J ((l : G)⁻¹ * ((m : G) * u * k), l) =
        conj (CompactInduction.integrand h hU A K ((l : G)⁻¹ * ((m : G) * u * k)) ψ l) *
          f ((l : G)⁻¹ * ((m : G) * u * k)) from rfl, enorm_mul, RCLike.enorm_conj]
      have he : CompactInduction.integrand h hU A K ((l : G)⁻¹ * ((m : G) * u * k)) ψ l =
          ((NNReal.sqrt (δ m) : ℝ) : ℂ) * coefficientTensorMap A t m := by
        change TensorProduct.lift (smoothDualPairing A.representation).flip
          (Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
            (productLeviObject A A.contragredient)) ψ
              ((l : G) * ((l : G)⁻¹ * ((m : G) * u * k)), (l : G))) = _
        rw [mul_inv_cancel_left]
        exact lift_eval_levi_mul h hU A hδU ψ m u k l
      rw [he, enorm_mul, ← ofReal_norm (((NNReal.sqrt (δ m) : ℝ) : ℂ)),
        Complex.norm_of_nonneg (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
      change D m * ‖coefficientTensorMap A t m‖ₑ * ‖f ((l : G)⁻¹ * ((m : G) * u * k))‖ₑ ≤ _
      calc _ ≤ D m * L m * ‖f ((l : G)⁻¹ * ((m : G) * u * k))‖ₑ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoeff zero_le) zero_le
        _ ≤ D m * L m * (B * W m u) := mul_le_mul_of_nonneg_left hf' zero_le
        _ = _ := by ring
    calc ∫⁻ u : U, ‖J ((l : G)⁻¹ * ((m : G) * u * k), l)‖ₑ ∂muU
        ≤ ∫⁻ u : U, (L m * B * D m) * W m u ∂muU := lintegral_mono hpt
      _ = L m * B * (D m * ∫⁻ u : U, W m u ∂muU) := by
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB.ne) ENNReal.coe_ne_top), mul_assoc]
      _ ≤ L m * B * ((c : ℝ≥0∞) * ENNReal.ofReal (ΞM m * (1 + σM m) ^ (-r))) :=
        mul_le_mul_of_nonneg_left (hct m) zero_le
      _ = T * E m := by
        have hs : 0 < 1 + σM m := by linarith [hwM.nonneg m]
        have hx : 0 ≤ ΞM m := (hwM.pos m).le
        have hnon (a : ℝ) : 0 ≤ ΞM m * (1 + σM m) ^ a :=
          mul_nonneg hx (Real.rpow_nonneg hs.le _)
        unfold L T E
        rw [ENNReal.ofReal_mul hC.le]
        calc _ = ENNReal.ofReal C * B * (c : ℝ≥0∞) *
            (ENNReal.ofReal (ΞM m * (1 + σM m) ^ R) *
              ENNReal.ofReal (ΞM m * (1 + σM m) ^ (-r))) := by ring
          _ = _ := by
            rw [← ENNReal.ofReal_mul (hnon R)]
            congr 2
            rw [show ΞM m * (1 + σM m) ^ R * (ΞM m * (1 + σM m) ^ (-r)) =
                ΞM m ^ 2 * ((1 + σM m) ^ R * (1 + σM m) ^ (-r)) by ring,
              ← Real.rpow_add hs, show R + -r = -hwM.exponent by unfold r; ring]
  have hs (l : K) : ∫⁻ g, ‖J (g, l)‖ₑ ∂mu ≤ T * hwM.const := by
    let F (g : G) := ‖J ((l : G)⁻¹ * g, l)‖ₑ
    have hF : Measurable F := (hJ.comp
      ((continuous_const.mul continuous_id).prodMk continuous_const)).measurable.enorm
    have htranslate : ∫⁻ g, ‖J (g, l)‖ₑ ∂mu = ∫⁻ g, F g ∂mu :=
      (lintegral_mul_left_eq_self (fun g => ‖J (g, l)‖ₑ) (l : G)⁻¹).symm
    rw [htranslate, lintegral_eq_lintegral_levi_unipotent h.levi_le_normalizer K.isOpen.measurableSet
      hfac hsplit hMK hUK F hF]
    calc ∫⁻ k in (K : Set G), ∫⁻ m, ∫⁻ u, F ((m : G) * u * k) ∂muU ∂muM ∂mu
        ≤ ∫⁻ k in (K : Set G), T * hwM.const ∂mu := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem K.isOpen.measurableSet (μ := mu)] with k hk
          refine (lintegral_mono fun m => hslice l k hk m).trans_eq ?_
          rw [lintegral_const_mul' _ _ hTfin]
          rfl
      _ = T * hwM.const := by rw [lintegral_const, Measure.restrict_apply_univ, hμK, mul_one]
  refine ⟨hJ.aestronglyMeasurable, ?_⟩
  change ∫⁻ x, ‖J x‖ₑ ∂mu.prod (CompactInduction.measure K hK) < ⊤
  rw [lintegral_prod_symm' _ hJ.measurable.enorm]
  calc ∫⁻ l : K, ∫⁻ g, ‖J (g, l)‖ₑ ∂mu ∂CompactInduction.measure K hK
      ≤ ∫⁻ _ : K, T * hwM.const ∂CompactInduction.measure K hK := lintegral_mono hs
    _ = T * hwM.const := by rw [lintegral_const, measure_univ, mul_one]
    _ < ⊤ := ENNReal.mul_lt_top hTfin.lt_top hwM.const_lt_top

end Convergence

section Rational

open _root_.CategoryTheory _root_.AlgebraicGeometry Langlands.GroupScheme RationalSemistandard
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type uG} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  {ν : cocharacterLattice S} (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (p : SemistandardSpectralIndex i) (d : CompactData p)
  (A : SmoothRep.{0, uG, uV} ℂ (levi p))
  {muG : Measure (rationalPoints G)} [SFinite muG] [muG.IsMulLeftInvariant]
  {muL : Measure (levi p)} [SFinite muL] [muL.IsMulLeftInvariant]
  {muU : Measure (radical p)} [SFinite muU] [muU.IsMulLeftInvariant]
  {XiM sigmaM : levi p → ℝ}

include hG hi in
set_option maxHeartbeats 2000000 in
/-- The double-integrability field of the actual semistandard Fourier
regularity interface follows from the stated Iwasawa and Levi estimates. -/
theorem rationalSemistandardFourierDoubleIntegrability
    (hmu : muG (d.compact : Set (rationalPoints G)) = 1)
    (hMK : muL {m : levi p | (m : rationalPoints G) ∈ d.compact} = 1)
    (hUK : muU {u : radical p | (u : rationalPoints G) ∈ d.compact} = 1)
    (hsplit : ∀ (m : levi p) (u : radical p), (m : rationalPoints G) * u ∈ d.compact ↔
      (m : rationalPoints G) ∈ d.compact ∧ (u : rationalPoints G) ∈ d.compact)
    (hE : ConstantTermEstimate muU
      (HaarModulus.closedRestrictCharacter (radical p) (isClosed_radical p) (levi p)
        (decomposition p).levi_le_normalizer)
      (rationalXi hKc hPK) (rationalHeight (F := F) ρ) XiM sigmaM)
    (hwM : L2Weights muL XiM sigmaM) (hT : HasTemperedCoefficients XiM sigmaM A.representation)
    (f : RationalSchwartzSpace hKc hPK ρ)
    (ψ : productInducedCoefficientObject (decomposition p) (isClosed_radical p) A) :
    Integrable (fun x : rationalPoints G × d.compact =>
      conj (CompactInduction.integrand (decomposition p) (isClosed_radical p) A
        d.compact x.1 ψ x.2) * f x.1)
      (muG.prod (CompactInduction.measure d.compact d.isCompact)) := by
  let r := CocharacterPresentation.ofCoverage hG semistandardSpectralDynamicCoverage hi p
  exact constantTermFourierDoubleIntegrability (decomposition p) (isClosed_radical p)
    A d.compact d.isCompact (radical_isUnimodular hG r) d.factorization_mem hsplit
    hmu hMK hUK hE (rationalTranslationWeights K.isOpen hKc hPK ρ) hwM hT ψ f

end Rational

end Langlands.HarishChandraSchwartz
