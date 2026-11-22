import Langlands.Global.RankinSelberg.ComplexNormalizedApproximation
import Langlands.Global.RankinSelberg.ComplexWhittakerTranslatedMellin
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Normalized unequal-rank evaluation on right translates -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexUnequalTranslatedNormalization

open Langlands.Archimedean (continuous_unitary_toUnits)
open Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal
open ComplexGodement (compactMatrixHaar)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexJacquet (CauchyOnRightVerticalLines complexPairNormalizedApproximation complexCentralSign_sq
  HasComplexPairNormalizedGrowth)
open ComplexUnequalFamily (HasLeftCharacter HalfPlaneDomination ordinary_halfPlaneDomination
  dual_halfPlaneDomination continuous_ordinaryKernel continuous_dualKernel dualIntegral_eq_prod
  differentiableOn_integral_of_halfPlaneDomination)
open ComplexUnequalMellinReduction (quotientDetAbs quotientDetAbs_pos
  complexUnequalIntegrand_eq_mul complexUnequalDualKernel_eq_mul)
open ComplexWhittakerRightTranslateApproximation (complexWhittakerRightTranslateApproximation)
open ComplexWhittakerTranslatedMellin (compact_rightTranslate_uniformSimpleRootBound)

attribute [local instance] archimedeanComplexGLMeasurable archimedeanComplexGLBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel
  archimedeanComplexQMeasurable archimedeanComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "KU" => fun n => Matrix.unitaryGroup (Fin n) ℂ
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "R" => fun r t => Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ
local notation "Std" => Automorphic.complexStandardKFinite
local notation "ρ" => ArchimedeanLocal.translateFunction

local instance approxUnitaryMeasurable (n : ℕ) : MeasurableSpace (KU n) := borel _
local instance approxUnitaryBorel (n : ℕ) : BorelSpace (KU n) := ⟨rfl⟩

private theorem mellinApproximation {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℂ) (f₀ : X → ℂ) (δ : X → ℝ) (hδ : ∀ q, 0 < δ q) (σ : ℝ)
    (hM : ∀ (n : ℕ) (s : ℂ), AEStronglyMeasurable (fun q => f n q * (δ q : ℂ) ^ s) μ)
    (hdom : HalfPlaneDomination μ (univ : Set (ℕ × ℂ)) Prod.snd
      (fun p q => f p.1 q * (δ q : ℂ) ^ p.2) σ)
    (hlim : ∀ q, Tendsto (fun n => f n q) atTop (𝓝 (f₀ q))) :
    let I n (s : ℂ) := ∫ q, f n q * (δ q : ℂ) ^ s ∂μ
    (∀ n, DifferentiableOn ℂ (I n) {s : ℂ | σ < s.re}) ∧
    CauchyOnRightVerticalLines σ I ∧
    ∀ s : ℂ, σ < s.re → Tendsto (fun n => I n s) atTop
      (𝓝 (∫ q, f₀ q * (δ q : ℂ) ^ s ∂μ)) := by
  let F (n : ℕ) (s : ℂ) (q : X) := f n q * (δ q : ℂ) ^ s
  let F₀ (s : ℂ) (q : X) := f₀ q * (δ q : ℂ) ^ s
  let I n s := ∫ q, F n s q ∂μ
  change (∀ n, DifferentiableOn ℂ (I n) {s : ℂ | σ < s.re}) ∧ CauchyOnRightVerticalLines σ I ∧ _
  have hDI (n : ℕ) : (∀ s : ℂ, σ < s.re → Integrable (F n s) μ) ∧
      DifferentiableOn ℂ (I n) {s : ℂ | σ < s.re} := by
    have hB : HalfPlaneDomination μ (univ : Set ℂ) id (F n) σ := by
      intro b
      obtain ⟨M, hM₀, hMb⟩ := hdom b
      exact ⟨M, hM₀, fun s _ hs hs' => hMb (n, s) trivial hs hs'⟩
    have hDiff (q : X) : Differentiable ℂ (fun s => F n s q) :=
      (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (hδ q).ne'))).const_mul _
    obtain ⟨hint, hdif⟩ := differentiableOn_integral_of_halfPlaneDomination
      (s := id) isOpen_univ differentiable_id (hM n) (fun q => (hDiff q).differentiableOn) hB
    exact ⟨fun s hs => hint s ⟨mem_univ _, hs⟩, hdif.mono fun _ hs => ⟨mem_univ _, hs⟩⟩
  have hPt (s : ℂ) (q : X) : Tendsto (fun n => F n s q) atTop (𝓝 (F₀ s q)) :=
    (hlim q).mul tendsto_const_nhds
  refine ⟨fun n => (hDI n).2, ?_, ?_⟩
  · intro b hb ε hε
    let z : ℂ := b
    have hz : σ < z.re := by simpa only [z, Complex.ofReal_re] using hb
    obtain ⟨B, hB, hbnd⟩ := hdom b
    have hB₁ (n : ℕ) (q : X) : ‖F n z q‖ ≤ B q :=
      hbnd (n, z) trivial hz (by simp [z]) q
    have hB₀ (q : X) : ‖F₀ z q‖ ≤ B q :=
      le_of_tendsto (hPt z q).norm (Eventually.of_forall fun n => hB₁ n q)
    have hF₀ : AEStronglyMeasurable (F₀ z) μ :=
      aestronglyMeasurable_of_tendsto_ae atTop (fun n => hM n z) (ae_of_all _ (hPt z))
    have hJ₀ : Integrable (F₀ z) μ := hB.mono' hF₀ (ae_of_all _ hB₀)
    let D n := ∫ q, ‖F n z q - F₀ z q‖ ∂μ
    have hD : Tendsto D atTop (𝓝 0) := by
      have hc (q : X) : Tendsto (fun n => ‖F n z q - F₀ z q‖) atTop (𝓝 (0 : ℝ)) := by
        simpa only [sub_self, norm_zero] using ((hPt z q).sub (tendsto_const_nhds (x := F₀ z q))).norm
      have h := tendsto_integral_of_dominated_convergence (fun q => 2 * B q)
        (fun n => ((hM n z).sub hF₀).norm) (hB.const_mul 2)
        (fun n => ae_of_all _ fun q => by
          rw [Real.norm_of_nonneg (norm_nonneg _), two_mul]
          exact (norm_sub_le _ _).trans (add_le_add (hB₁ n q) (hB₀ q))) (ae_of_all _ hc)
      simpa only [integral_zero, D, F, Pi.sub_apply] using h
    obtain ⟨k, hk⟩ := eventually_atTop.1 (hD.eventually (eventually_lt_nhds (half_pos hε)))
    refine ⟨k, fun n m hn hm s hs => ?_⟩
    have hsl : σ < s.re := by rwa [hs]
    have hNorm (q : X) : ‖F n s q - F m s q‖ = ‖F n z q - F m z q‖ := by
      simp only [F, ← sub_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hδ q), hs,
        z, Complex.ofReal_re]
    have hTri (q : X) : ‖F n z q - F m z q‖ ≤ ‖F n z q - F₀ z q‖ + ‖F m z q - F₀ z q‖ := by
      simpa only [dist_eq_norm] using dist_triangle_right (F n z q) (F m z q) (F₀ z q)
    have hDn := (((hDI n).1 z hz).sub hJ₀).norm
    have hDm := (((hDI m).1 z hz).sub hJ₀).norm
    calc
      ‖I n s - I m s‖ = ‖∫ q, F n s q - F m s q ∂μ‖ := by
        rw [integral_sub ((hDI n).1 s hsl) ((hDI m).1 s hsl)]
      _ ≤ ∫ q, ‖F n s q - F m s q‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ q, ‖F n z q - F m z q‖ ∂μ := integral_congr_ae (ae_of_all _ hNorm)
      _ ≤ ∫ q, ‖F n z q - F₀ z q‖ + ‖F m z q - F₀ z q‖ ∂μ :=
        integral_mono (((hDI n).1 z hz).sub ((hDI m).1 z hz)).norm (hDn.add hDm) hTri
      _ = D n + D m := integral_add hDn hDm
      _ ≤ ε := by linarith [hk n hn, hk m hm]
  · intro s hs
    obtain ⟨B, hB, hb⟩ := hdom s.re
    exact tendsto_integral_of_dominated_convergence B (fun n => hM n s) hB
      (fun n => ae_of_all _ (hb (n, s) trivial hs le_rfl)) (ae_of_all _ (hPt s))

private theorem rootBound_compactApproximants {r : ℕ} {ds : List ComplexCharacterData} {a : ℂˣ}
    (W : complexWhittakerModel r ds a) (g : G (r + 1))
    (U : ℕ → complexWhittakerModel r ds a) (w : ℕ → KU (r + 1) → ℝ)
    (hw : ∀ n, Continuous (w n)) (hw₀ : ∀ n k, 0 ≤ w n k)
    (hw₁ : ∀ n, (∫ k, w n k ∂compactMatrixHaar (r + 1)) = 1)
    (hU : ∀ n x, (U n).val x = ∫ k, (w n k : ℂ) * W.val (x * Unitary.toUnits k * g)
      ∂compactMatrixHaar (r + 1)) :
    HasUniformSimpleRootBound (univ : Set (ℕ × ℂ)) (fun p => (U p.1).val) := by
  let S := Set.range fun k : KU (r + 1) => Unitary.toUnits k * g
  obtain ⟨N, hN⟩ := compact_rightTranslate_uniformSimpleRootBound W S
    (isCompact_range (continuous_unitary_toUnits.mul_const g))
  refine ⟨N, fun J => ?_⟩
  obtain ⟨C, hC, hC'⟩ := hN J
  refine ⟨C, hC, fun p _ x => ?_⟩
  let M := C * Real.exp ((N : ℝ) * (∑ i, |ComplexLocalIwasawa.alpha x i|) -
    (J : ℝ) * RealConvergenceAnalysis.rootPos (ComplexLocalIwasawa.alpha x))
  have hwI : Integrable (w p.1) (compactMatrixHaar (r + 1)) :=
    (hw p.1).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  change ‖(U p.1).val x‖ ≤ M
  rw [hU]
  calc
    _ ≤ ∫ k, w p.1 k * M ∂compactMatrixHaar (r + 1) := by
      apply norm_integral_le_of_norm_le (hwI.mul_const M)
      exact ae_of_all _ fun k => by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw₀ p.1 k), mul_assoc]
        exact mul_le_mul_of_nonneg_left (hC' _ ⟨k, rfl⟩ x) (hw₀ p.1 k)
    _ = M := by rw [integral_mul_const, hw₁, one_mul]

/-- The entire ordinary normalization of a genuine right translate is the locally
uniform limit of entire normalizations of compact-finite tests. -/
def ComplexUnequalTranslatedNormalizationStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (ds es : List ComplexCharacterData) (a : ℂˣ) (D : ComplexQuotientMeasureData t),
    (∀ (W : complexWhittakerModel r ds a) (V : complexWhittakerModel t es (-a)),
      HasComplexPairNormalizedGrowth ds es a (complexCentralSign es ^ r)
        (complexUnequalIntegral h D W.val V.val) (complexUnequalDualIntegral h a D W.val V.val)) →
    ∀ (B : Std (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)), IsComplexWhittakerIntertwiner r ds a B →
    ∀ (v : Std (r + 1) ds) (g : G (r + 1)) (V : complexWhittakerModel t es (-a)),
    ∃ (U : ℕ → complexWhittakerModel r ds a) (N : ℕ → ℂ → ℂ) (N₀ : ℂ → ℂ) (σ : ℝ),
      (∀ n, Differentiable ℂ (N n)) ∧
      (∀ n s, σ < s.re → N n s = (complexPairLFactor ds es).denominator s *
        complexUnequalIntegral h D (U n).val V.val s) ∧
      TendstoLocallyUniformly N N₀ atTop ∧ Differentiable ℂ N₀ ∧ HasStripExponentialGrowth N₀ ∧
      ∀ s : ℂ, σ < s.re → N₀ s = (complexPairLFactor ds es).denominator s *
        complexUnequalIntegral h D (ρ g (B v)) V.val s

set_option maxHeartbeats 1100000 in
theorem complexUnequalTranslatedNormalization : ComplexUnequalTranslatedNormalizationStatement := by
  intro r t h ds es a D hPair B hB v g V
  obtain ⟨U, w, hw, hw₀, hw₁, hu, hlim⟩ := complexWhittakerRightTranslateApproximation r ds a B hB v g
  let W : complexWhittakerModel r ds a :=
    ⟨B v, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)⟩
  let A (p : ℕ × ℂ) := (U p.1).val
  let C (_ : ℕ × ℂ) := V.val
  have hA : ∀ p, HasLeftCharacter a (A p) :=
    fun p u x => complexWhittakerModel_left_equivariant (U p.1).2 u.val u.2 x
  have hC : ∀ p, HasLeftCharacter (-a) (C p) :=
    fun _ u x => complexWhittakerModel_left_equivariant V.2 u.val u.2 x
  have hAb : HasUniformSimpleRootBound univ A := rootBound_compactApproximants W g U w hw hw₀ hw₁ hu
  have hCb : HasUniformSimpleRootBound univ C := by
    obtain ⟨N, hN⟩ := compact_rightTranslate_uniformSimpleRootBound V {1} isCompact_singleton
    refine ⟨N, fun J => ?_⟩
    obtain ⟨M, hM, hM'⟩ := hN J
    exact ⟨M, hM, fun _ _ x => by simpa only [C, mul_one] using hM' 1 (mem_singleton _) x⟩
  obtain ⟨b, hb⟩ := ordinary_halfPlaneDomination h D univ A C Prod.snd hA hC hAb hCb
  obtain ⟨bd, hbd⟩ := dual_halfPlaneDomination h a D univ A C Prod.snd hA hC hAb hCb
  let σ := max b bd
  let f n := complexUnequalIntegrand h (U n).val V.val 0
  let f₀ := complexUnequalIntegrand h (ρ g (B v)) V.val 0
  let fd n := complexUnequalDualKernel h (U n).val V.val 0
  let fd₀ := complexUnequalDualKernel h (ρ g (B v)) V.val 0
  let μ := D.measure
  let ν := complexUnequalDualMeasure (r := r) a D
  have hfo n s q : f n q * (quotientDetAbs q : ℂ) ^ s = complexUnequalIntegrand h (U n).val V.val s q :=
    (complexUnequalIntegrand_eq_mul h _ _ s q).symm
  have hfd n s (p : Q t × R r t) : fd n p * (quotientDetAbs p.1 : ℂ) ^ s =
      complexUnequalDualKernel h (U n).val V.val s p := (complexUnequalDualKernel_eq_mul h _ _ s p).symm
  have hUc (n : ℕ) : Continuous (U n).val := (contMDiff_of_mem_complexWhittakerModel (U n).2).continuous
  have hVc : Continuous V.val := (contMDiff_of_mem_complexWhittakerModel V.2).continuous
  have hM (n : ℕ) (s : ℂ) : AEStronglyMeasurable (fun q => f n q * (quotientDetAbs q : ℂ) ^ s) μ := by
    simp_rw [hfo]
    exact (continuous_ordinaryKernel h (hA (n, s)) (hC (n, s)) (hUc n) hVc s).aestronglyMeasurable
  have hMd (n : ℕ) (s : ℂ) : AEStronglyMeasurable
      (fun p : Q t × R r t => fd n p * (quotientDetAbs p.1 : ℂ) ^ s) ν := by
    simp_rw [hfd]
    exact (continuous_dualKernel h (hA (n, s)) (hC (n, s)) (hUc n) hVc s).aestronglyMeasurable
  have hdom : HalfPlaneDomination μ (univ : Set (ℕ × ℂ)) Prod.snd
      (fun p q => f p.1 q * (quotientDetAbs q : ℂ) ^ p.2) σ := by
    intro τ
    obtain ⟨K, hK, hK'⟩ := hb τ
    refine ⟨K, hK, fun p hp hs hτ q => ?_⟩
    dsimp only
    rw [hfo]
    exact hK' p hp ((le_max_left b bd).trans_lt hs) hτ q
  have hdomd : HalfPlaneDomination ν (univ : Set (ℕ × ℂ)) Prod.snd
      (fun p q => fd p.1 q * (quotientDetAbs q.1 : ℂ) ^ p.2) σ := by
    intro τ
    obtain ⟨K, hK, hK'⟩ := hbd τ
    refine ⟨K, hK, fun p hp hs hτ q => ?_⟩
    dsimp only
    rw [hfd]
    exact hK' p hp ((le_max_right b bd).trans_lt hs) hτ q
  have hlimf (q : Q t) : Tendsto (fun n => f n q) atTop (𝓝 (f₀ q)) := by
    unfold f f₀ complexUnequalIntegrand ArchimedeanLocal.unequalIntegrand ArchimedeanLocal.translateFunction
    exact ((hlim _).mul tendsto_const_nhds).mul tendsto_const_nhds
  have hlimfd (p : Q t × R r t) : Tendsto (fun n => fd n p) atTop (𝓝 (fd₀ p)) := by
    unfold fd fd₀ complexUnequalDualKernel ArchimedeanLocal.blockKernel ArchimedeanLocal.translateFunction
      ArchimedeanLocal.dualFunction
    exact ((hlim _).mul tendsto_const_nhds).mul tendsto_const_nhds
  obtain ⟨hDiff, hCauchy, hOrdLim⟩ := mellinApproximation μ f f₀ quotientDetAbs quotientDetAbs_pos σ hM hdom hlimf
  obtain ⟨hDiffd, hCauchyd, _⟩ := mellinApproximation ν fd fd₀ (fun p => quotientDetAbs p.1)
    (fun p => quotientDetAbs_pos p.1) σ hMd hdomd hlimfd
  have hOrdEq (n : ℕ) (s : ℂ) : complexUnequalIntegral h D (U n).val V.val s =
      ∫ q, f n q * (quotientDetAbs q : ℂ) ^ s ∂μ := by
    exact integral_congr_ae (ae_of_all _ fun q => (hfo n s q).symm)
  have hDualEq (n : ℕ) (s : ℂ) (hs : σ < s.re) : complexUnequalDualIntegral h a D (U n).val V.val s =
      ∫ p, fd n p * (quotientDetAbs p.1 : ℂ) ^ s ∂ν := by
    obtain ⟨K, hK, hK'⟩ := hdomd s.re
    have hint := hK.mono' (hMd n s) (ae_of_all _ (hK' (n, s) (mem_univ _) hs le_rfl))
    have hintegrable : Integrable (complexUnequalDualKernel h (U n).val V.val s) ν := by
      simpa only [hfd] using hint
    rw [dualIntegral_eq_prod h a D _ _ s hintegrable]
    exact integral_congr_ae (ae_of_all _ fun p => (hfd n s p).symm)
  have hOrdCauchy : CauchyOnRightVerticalLines σ (fun n => complexUnequalIntegral h D (U n).val V.val) := by
    simpa only [CauchyOnRightVerticalLines, hOrdEq] using hCauchy
  have hDualCauchy : CauchyOnRightVerticalLines σ (fun n => complexUnequalDualIntegral h a D (U n).val V.val) := by
    intro b hb ε hε
    obtain ⟨k, hk⟩ := hCauchyd b hb ε hε
    refine ⟨k, fun n m hn hm s hs => ?_⟩
    have hs' : σ < s.re := by rwa [hs]
    dsimp only
    rw [hDualEq n s hs', hDualEq m s hs']
    exact hk n m hn hm s hs
  have hc : complexCentralSign es ≠ 0 := by
    intro he
    have := complexCentralSign_sq es
    rw [he, zero_pow (by decide : (2 : ℕ) ≠ 0)] at this
    exact zero_ne_one this
  obtain ⟨N, N₀, hN, hNR, hNlim, hN₀, hN₀g, hN₀R⟩ := complexPairNormalizedApproximation ds es a _
    (pow_ne_zero _ hc) σ _ _ (complexUnequalIntegral h D (ρ g (B v)) V.val)
    (fun n => hPair (U n) V) (fun n => (hDiff n).congr fun s _ => hOrdEq n s)
    (fun n => (hDiffd n).congr fun s hs => hDualEq n s hs) hOrdCauchy hDualCauchy (by
      intro s hs
      have he : (∫ q, f₀ q * (quotientDetAbs q : ℂ) ^ s ∂μ) =
          complexUnequalIntegral h D (ρ g (B v)) V.val s :=
        integral_congr_ae (ae_of_all _ fun q => (complexUnequalIntegrand_eq_mul h _ _ s q).symm)
      simpa only [hOrdEq, he] using hOrdLim s hs)
  exact ⟨U, N, N₀, σ, hN, hNR, hNlim, hN₀, hN₀g, hN₀R⟩

end Langlands.Global.RankinSelbergGlobal.ComplexUnequalTranslatedNormalization
