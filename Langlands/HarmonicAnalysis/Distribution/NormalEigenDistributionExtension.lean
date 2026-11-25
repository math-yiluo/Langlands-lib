import Langlands.HarmonicAnalysis.Distribution.FlatNormalCutoffLimit
import Langlands.HarmonicAnalysis.Distribution.VanishingFieldJetFlattening

/-! # Extension of punctured eigen-distributions on compact supports -/

noncomputable section

open Filter Function Set TopologicalSpace
open scoped ContDiff Distributions NNReal Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis

universe u v

variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens X}

private theorem exists_contDiff_eqOn_compact {f : X → F} (hf : ContDiffOn ℝ ∞ f Ω)
    {K : Compacts X} (hK : (K : Set X) ⊆ Ω) :
    ∃ g : X → F, ContDiff ℝ ∞ g ∧ EqOn g f K := by
  obtain ⟨s, hs, hKs, hsΩ⟩ := normal_exists_closure_subset K.isCompact.isClosed Ω.isOpen hK
  obtain ⟨χ, hχ, _, hχs, hχK⟩ := exists_contDiff_support_eq_eq_one_iff hs
    K.isCompact.isClosed hKs (n := (⊤ : ℕ∞))
  refine ⟨fun x => χ x • f x, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ Ω
    · exact hχ.contDiffAt.smul (hf.contDiffAt (Ω.isOpen.mem_nhds hx))
    · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      have hx' : x ∈ (closure s)ᶜ := fun h => hx (hsΩ h)
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx'] with y hy
      rw [show χ y = 0 from notMem_support.mp (fun h => hy (subset_closure (hχs ▸ h))), zero_smul]
  · intro x hx
    change χ x • f x = f x
    rw [(hχK x).mp hx, one_smul]

variable {W : X → X} {b : X → ℝ} {K : Compacts X}

/-- The shifted field acts continuously on tests with a fixed compact support. -/
def fixedSupportShiftedField (hW : ContDiffOn ℝ ∞ W Ω) (hb : ContDiffOn ℝ ∞ b Ω)
    (hK : (K : Set X) ⊆ Ω) : 𝓓_{K}(X, ℝ) →L[ℝ] 𝓓_{K}(X, ℝ) :=
  let W₀ := (exists_contDiff_eqOn_compact hW hK).choose
  let b₀ := (exists_contDiff_eqOn_compact hb hK).choose
  ((ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.apply ℝ ℝ (E' := X)).flip
    (g := W₀) (exists_contDiff_eqOn_compact hW hK).choose_spec.1).comp
    (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤)) +
    ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ)
      (g := b₀) (exists_contDiff_eqOn_compact hb hK).choose_spec.1

@[simp] theorem fixedSupportShiftedField_apply (hW : ContDiffOn ℝ ∞ W Ω)
    (hb : ContDiffOn ℝ ∞ b Ω) (hK : (K : Set X) ⊆ Ω) (f : 𝓓_{K}(X, ℝ)) (x : X) :
    fixedSupportShiftedField hW hb hK f x = fderiv ℝ f x (W x) + f x * b x := by
  let W₀ := (exists_contDiff_eqOn_compact hW hK).choose
  let b₀ := (exists_contDiff_eqOn_compact hb hK).choose
  change (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤ f : 𝓓_{K}(X, X →L[ℝ] ℝ)) x (W₀ x) +
    f x * b₀ x = _
  rw [ContDiffMapSupportedIn.fderivCLM_apply_of_le ℝ f (by simp)]
  by_cases hx : x ∈ K
  · have hw : W₀ x = W x := (exists_contDiff_eqOn_compact hW hK).choose_spec.2 hx
    have hc : b₀ x = b x := (exists_contDiff_eqOn_compact hb hK).choose_spec.2 hx
    rw [hw, hc]
  · have hs : x ∉ tsupport f := fun h => hx (f.tsupport_subset h)
    have hf : f x = 0 := f.zero_on_compl hx
    simp only [fderiv_of_notMem_tsupport ℝ hs, zero_apply, hf, zero_mul]

private theorem ofSupportedIn_iterate_shiftedField (hW : ContDiffOn ℝ ∞ W Ω)
    (hb : ContDiffOn ℝ ∞ b Ω) (hK : (K : Set X) ⊆ Ω) {Ω' : Opens X} (h' : Ω' ≤ Ω)
    (hK' : (K : Set X) ⊆ Ω') (f : 𝓓_{K}(X, ℝ)) (p : ℕ) :
    TestFunction.ofSupportedIn hK' ((fixedSupportShiftedField hW hb hK)^[p] f) =
      (shiftedVectorFieldDerivativeTest (hW.mono h') (hb.mono h'))^[p] (TestFunction.ofSupportedIn hK' f) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    ext x
    exact fixedSupportShiftedField_apply hW hb hK _ x

variable {E : Type u} {N : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]

local notation "X₀" => E × N
local notation "pK(" K "|" k ")" => ContDiffMapSupportedIn.supSeminorm ℝ X₀ ℝ ⊤ K k

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ N] in
private theorem norm_deriv_le_supSeminorm {K : Compacts X₀} (f : 𝓓_{K}(X₀, ℝ))
    {i m : ℕ} (hi : i ≤ m) (x : X₀) : ‖iteratedFDeriv ℝ i f x‖ ≤ pK(K | m) f :=
  (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
    ((Finset.le_sup (f := ContDiffMapSupportedIn.seminorm ℝ X₀ ℝ ⊤ K)
      (Finset.mem_Iic.mpr hi)) f)

omit [FiniteDimensional ℝ E] in
private theorem exists_bound_puncturedCutoffSequence {Ω : Opens X₀} {K : Compacts X₀}
    (hK : (K : Set X₀) ⊆ Ω) (d m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : 𝓓_{K}(X₀, ℝ)),
      (∀ x : E, ∀ i ≤ d + m, iteratedFDeriv ℝ i f (x, 0) = 0) →
      ∀ n j : ℕ, j ≤ d → ∀ x : X₀,
        ‖iteratedFDeriv ℝ j (puncturedCutoffSequence hK f n) x‖ ≤
          (C * pK(K | (d + m + 1)) f) * ‖x.2‖ ^ m := by
  obtain ⟨C, hC, hC'⟩ := exists_weighted_normalCutoff_bound (E := E) (N := N) d m
  refine ⟨1 + C, by positivity, fun f hf n j hj x => ?_⟩
  let s : ℝ := (n : ℝ) + 1
  let q := pK(K | (d + m + 1)) f
  have hq : 0 ≤ q := apply_nonneg _ _
  have hs : 1 ≤ s := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hF := norm_iteratedFDeriv_le_pow_of_flat f.contDiff (x.1, 0) (d + m) hq
    (hf x.1) (fun _ hl y => norm_deriv_le_supSeminorm f hl y) m j (by omega) x
  have hx : ‖x - (x.1, 0)‖ = ‖x.2‖ := by simp [Prod.norm_def]
  rw [hx] at hF
  have hCut := hC' f hf s hs j hj x
  have he : (puncturedCutoffSequence hK f n : X₀ → ℝ) =
      (f : X₀ → ℝ) - (normalCutoffTest s f : X₀ → ℝ) := rfl
  rw [he, iteratedFDeriv_sub_apply (f.contDiff.contDiffAt.of_le (by simp))
    ((normalCutoffTest s f).contDiff.contDiffAt.of_le (by simp))]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j f x‖ + ‖iteratedFDeriv ℝ j (normalCutoffTest s f) x‖ := norm_sub_le _ _
    _ ≤ q * ‖x.2‖ ^ m + (C * q) * ‖x.2‖ ^ m * s⁻¹ := add_le_add hF hCut
    _ ≤ q * ‖x.2‖ ^ m + (C * q) * ‖x.2‖ ^ m * 1 := by
      gcongr
      exact inv_le_one_of_one_le₀ hs
    _ = _ := by ring

omit [FiniteDimensional ℝ E] in
private theorem tendsto_eval_puncturedCutoffSequence {Ω : Opens X₀} {K : Compacts X₀}
    (hK : (K : Set X₀) ⊆ Ω) (T₀ : 𝓓'(Ω, ℂ)) {m : ℕ}
    {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ f, ‖T₀ (TestFunction.ofSupportedIn hK f)‖ ≤ C * pK(K | m) f)
    (f : 𝓓_{K}(X₀, ℝ))
    (hf : ∀ x : E, ∀ i ≤ m, iteratedFDeriv ℝ i f (x, 0) = 0) :
    Tendsto (fun n => T₀ (TestFunction.monoCLM ℝ (puncturedCutoffSequence hK f n)))
      atTop (𝓝 (T₀ (TestFunction.ofSupportedIn hK f))) := by
  let s (n : ℕ) : ℝ := (n : ℝ) + 1
  let q := pK(K | (m + 1)) f
  have hq : 0 ≤ q := apply_nonneg _ _
  obtain ⟨B, hB, hB'⟩ := exists_weighted_normalCutoff_bound (E := E) (N := N) m 0
  have hCut (n : ℕ) : pK(K | m) (normalCutoffTest (s n) f) ≤ (B * q) * (s n)⁻¹ := by
    have hpos : 0 ≤ (B * q) * (s n)⁻¹ := by dsimp only [s]; positivity
    apply Seminorm.finset_sup_apply_le hpos
    intro j hj
    apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ hpos j _).mpr
    intro x _
    simpa only [Nat.add_zero, pow_zero, mul_one] using
      hB' f (by simpa only [Nat.add_zero] using hf) (s n)
        (le_add_of_nonneg_left (Nat.cast_nonneg n)) j (Finset.mem_Iic.mp hj) x
  have hlim : Tendsto (fun n => (s n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hT : Tendsto (fun n => T₀ (TestFunction.ofSupportedIn hK (normalCutoffTest (s n) f)))
      atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [sub_zero] using squeeze_zero (fun _ => norm_nonneg _) (fun n =>
      (hBound _).trans (mul_le_mul_of_nonneg_left (hCut n) hC)) (by
        simpa only [mul_zero, mul_assoc] using hlim.const_mul (C * (B * q)))
  have hmono : normalPuncturedDomain Ω ≤ Ω := inter_subset_left
  have he (n : ℕ) : (TestFunction.monoCLM ℝ (puncturedCutoffSequence hK f n) : 𝓓(Ω, ℝ)) =
      TestFunction.ofSupportedIn hK (f - normalCutoffTest (s n) f) := by
    ext x
    have h : ((TestFunction.monoCLM ℝ (puncturedCutoffSequence hK f n) : 𝓓(Ω, ℝ)) : X₀ → ℝ) =
        puncturedCutoffSequence hK f n := by simp [hmono]
    exact congrFun h x
  have ht := tendsto_const_nhds.sub hT (a := T₀ (TestFunction.ofSupportedIn hK f))
  refine (by simpa only [sub_zero] using ht : Tendsto
    (fun n => T₀ (TestFunction.ofSupportedIn hK f) -
      T₀ (TestFunction.ofSupportedIn hK (normalCutoffTest (s n) f)))
    atTop (𝓝 (T₀ (TestFunction.ofSupportedIn hK f)))).congr ?_
  intro n
  rw [he n]
  change T₀ _ - T₀ _ = T₀ (TestFunction.ofSupportedInCLM ℝ hK (f - normalCutoffTest (s n) f))
  rw [map_sub, map_sub]
  rfl

private theorem eval_iterate_shiftedField {Ω : Opens X₀} {W : X₀ → X₀} {b : X₀ → ℝ}
    (hW : ContDiffOn ℝ ∞ W Ω) (hb : ContDiffOn ℝ ∞ b Ω) (T : 𝓓'(Ω, ℂ)) (eigen : ℂ)
    (hEig : ∀ f, T (shiftedVectorFieldDerivativeTest hW hb f) = eigen * T f)
    (p : ℕ) (f : 𝓓(Ω, ℝ)) :
    T ((shiftedVectorFieldDerivativeTest hW hb)^[p] f) = eigen ^ p * T f := by
  induction p with
  | zero => simp
  | succ p ih => rw [Function.iterate_succ_apply', hEig, ih, pow_succ', mul_assoc]

/-- Extend a holomorphic family of punctured eigen-distributions to tests on one compact
support. The normalized cutoff limit agrees with the original evaluation on a test whose
support avoids the section. It also agrees with any already defined eigen-distribution
with a sufficiently low compact order and the same punctured restriction. -/
theorem exists_fixedSupportNormalEigenExtension {Ω : Opens X₀} {W : X₀ → X₀} {b : X₀ → ℝ}
    (hW : ContDiffOn ℝ ∞ W Ω) (hb : ContDiffOn ℝ ∞ b Ω) {K : Compacts X₀}
    (hK : (K : Set X₀) ⊆ Ω)
    (hZero : ∀ x : E, (x, (0 : N)) ∈ Ω → W (x, 0) = 0 ∧ b (x, 0) = 0)
    (hNil : ∀ x : E, (x, (0 : N)) ∈ Ω → IsNilpotent (fderiv ℝ W (x, 0)).toLinearMap)
    {S : Set ℂ} (hS : IsOpen S) (T : ℂ → 𝓓'(normalPuncturedDomain Ω, ℂ))
    {d m : ℕ} {A : ℝ} (hA : 0 ≤ A) (hT : ∀ z ∈ S, HasWeightedNormalBound (T z) K d m A)
    (hHol : ∀ g : 𝓓(normalPuncturedDomain Ω, ℝ), DifferentiableOn ℂ (fun z => T z g) S)
    (eigen : ℂ) (heigen : eigen ≠ 0)
    (hEig : ∀ z ∈ S, ∀ g, T z (shiftedVectorFieldDerivativeTest
      (hW.mono ((inter_subset_left) : (normalPuncturedDomain Ω : Set X₀) ⊆ Ω))
      (hb.mono inter_subset_left) g) = eigen * T z g) :
    ∃ p order : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∃ L : ℂ → 𝓓_{K}(X₀, ℝ) →L[ℝ] ℂ,
      (∀ f, DifferentiableOn ℂ (fun z => L z f) S) ∧
      (∀ f z, z ∈ S → ‖L z f‖ ≤ C * pK(K | order) f) ∧
      (∀ f z, z ∈ S → Tendsto
        (fun n => (eigen ^ p)⁻¹ * T z (puncturedCutoffSequence hK
          ((fixedSupportShiftedField hW hb hK)^[p] f) n)) atTop (𝓝 (L z f))) ∧
      (∀ z ∈ S, ∀ (f : 𝓓_{K}(X₀, ℝ)) (hoff : tsupport f ⊆ normalPuncturedDomain Ω),
        L z f = T z ⟨f, f.contDiff, f.hasCompactSupport, hoff⟩) ∧
      ∀ z ∈ S, ∀ (T₀ : 𝓓'(Ω, ℂ)),
        (∀ g, T z g = T₀ (TestFunction.monoCLM ℝ g)) →
        (∀ g, T₀ (shiftedVectorFieldDerivativeTest hW hb g) = eigen * T₀ g) →
        ∀ C₀ : ℝ, 0 ≤ C₀ →
          (∀ f, ‖T₀ (TestFunction.ofSupportedIn hK f)‖ ≤ C₀ * pK(K | (d + m)) f) →
          ∀ f, L z f = T₀ (TestFunction.ofSupportedIn hK f) := by
  classical
  let D := fixedSupportShiftedField hW hb hK
  let Z : Set X₀ := (Ω : Set X₀) ∩ {x | x.2 = 0}
  have hZ (x : X₀) (hx : x ∈ Z) : W x = 0 ∧ b x = 0 := by
    rcases x with ⟨y, n⟩
    rcases hx with ⟨hy, rfl⟩
    exact hZero y hy
  have hZ' (x : X₀) (hx : x ∈ Z) : IsNilpotent (fderiv ℝ W x).toLinearMap := by
    rcases x with ⟨y, n⟩
    rcases hx with ⟨hy, rfl⟩
    exact hNil y hy
  obtain ⟨p, hp⟩ := exists_iterate_shiftedField_flat hW hb (Z := Z) inter_subset_left hZ hZ'
    (d + m + 1)
  let Q := D ^ p
  have hQ (f : 𝓓_{K}(X₀, ℝ)) : Q f = D^[p] f :=
    congrFun (FunLike.coe_pow_eq_iterate D p) f
  have hflat (f : 𝓓_{K}(X₀, ℝ)) (x : E) (i : ℕ) (hi : i ≤ d + m) :
      iteratedFDeriv ℝ i (Q f) (x, 0) = 0 := by
    by_cases hx : (x, (0 : N)) ∈ Ω
    · have h := congrArg (fun g : 𝓓(Ω, ℝ) => iteratedFDeriv ℝ i g (x, 0))
        (ofSupportedIn_iterate_shiftedField hW hb hK le_rfl hK f p)
      rw [hQ f]
      change (iteratedFDeriv ℝ i (D^[p] f) (x, 0)) = _ at h
      rw [h]
      exact hp _ _ ⟨hx, rfl⟩ i (Nat.lt_succ_of_le hi)
    · exact (Q f).iteratedFDeriv_zero_on_compl (fun hx' => hx (hK hx'))
  let cut (f : 𝓓_{K}(X₀, ℝ)) := puncturedCutoffSequence hK (Q f)
  choose value hLimit hAnalytic using fun f : 𝓓_{K}(X₀, ℝ) =>
    exists_holomorphicCutoffLimit hK hS T hA hT hHol (Q f) (hflat f)
  let c := (eigen ^ p)⁻¹
  let g (z : ℂ) (f : 𝓓_{K}(X₀, ℝ)) : ℂ := if z ∈ S then c * value f z else 0
  have hSeq (z : ℂ) (hz : z ∈ S) (f : 𝓓_{K}(X₀, ℝ)) :
      Tendsto (fun n => c * T z (cut f n)) atTop (𝓝 (g z f)) := by
    simpa only [g, ite_eq_left hz] using ((hLimit f).tendsto_at hz).const_mul c
  have hCutAdd (f f' : 𝓓_{K}(X₀, ℝ)) (n : ℕ) : cut (f + f') n = cut f n + cut f' n := by
    ext x
    let χ : ContDiffBump (0 : N) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
    let k := χ (((n : ℝ) + 1) • x.2)
    change Q (f + f') x - k * Q (f + f') x =
      Q f x - k * Q f x + (Q f' x - k * Q f' x)
    rw [map_add]
    change _ + _ - k * (_ + _) = _
    ring
  have hCutSmul (a : ℝ) (f : 𝓓_{K}(X₀, ℝ)) (n : ℕ) : cut (a • f) n = a • cut f n := by
    ext x
    let χ : ContDiffBump (0 : N) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
    let k := χ (((n : ℝ) + 1) • x.2)
    change Q (a • f) x - k * Q (a • f) x = a * (Q f x - k * Q f x)
    rw [map_smul]
    change a * _ - k * (a * _) = _
    ring
  let L₀ (z : ℂ) : 𝓓_{K}(X₀, ℝ) →ₗ[ℝ] ℂ :=
    { toFun := g z
      map_add' := fun f f' => by
        by_cases hz : z ∈ S
        · refine tendsto_nhds_unique (hSeq z hz _) (((hSeq z hz f).add (hSeq z hz f')).congr ?_)
          intro n
          rw [hCutAdd, map_add, mul_add]
        · simp [g, hz]
      map_smul' := fun a f => by
        by_cases hz : z ∈ S
        · refine tendsto_nhds_unique (hSeq z hz _) (((hSeq z hz f).const_smul a).congr ?_)
          intro n
          rw [hCutSmul, map_smul, mul_smul_comm]
        · simp [g, hz] }
  obtain ⟨B, hB, hCut⟩ := exists_bound_puncturedCutoffSequence hK d m
  let q := (pK(K | (d + m + 1))).comp Q.toLinearMap
  have hq : Continuous q := (Seminorm.continuous_finsetSup (s := Finset.Iic (d + m + 1))
    fun j _ => (ContDiffMapSupportedIn.withSeminorms ℝ X₀ ℝ ⊤ K).continuous_seminorm j).comp Q.continuous
  let R : ℝ := ‖c‖ * A * B
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hBound (z : ℂ) (f : 𝓓_{K}(X₀, ℝ)) : ‖L₀ z f‖ ≤ R * q f := by
    by_cases hz : z ∈ S
    · apply le_of_tendsto ((hSeq z hz f).norm)
      apply Eventually.of_forall
      intro n
      have he := hT z hz (cut f n) (tsupport_puncturedCutoffTest_subset hK (Q f) _ _)
        (B * q f) (mul_nonneg hB (apply_nonneg _ _)) (fun j hj x => hCut (Q f) (hflat f) n j hj x)
      rw [norm_mul]
      calc
        _ ≤ ‖c‖ * (A * (B * q f)) := mul_le_mul_of_nonneg_left he (norm_nonneg _)
        _ = _ := by dsimp only [R]; ring
    · change ‖g z f‖ ≤ _
      simp only [g, ite_eq_right hz, norm_zero]
      exact mul_nonneg hR (apply_nonneg _ _)
  obtain ⟨s, C₀, _, hSup⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℝ X₀ ℝ ⊤ K) q hq
  let order := s.sup id
  let p₀ := ContDiffMapSupportedIn.seminorm ℝ X₀ ℝ ⊤ K
  have hMono : s.sup p₀ ≤ (Finset.Iic order).sup p₀ := by
    apply Finset.sup_mono
    intro j hj
    exact Finset.mem_Iic.mpr (Finset.le_sup (f := id) hj)
  let C : ℝ≥0 := ⟨R * (C₀ : ℝ), mul_nonneg hR C₀.coe_nonneg⟩
  have hUnif (z : ℂ) (f : 𝓓_{K}(X₀, ℝ)) : ‖L₀ z f‖ ≤ (C : ℝ) * pK(K | order) f := by
    refine (hBound z f).trans ?_
    change R * q f ≤ (R * (C₀ : ℝ)) * ((Finset.Iic order).sup p₀) f
    calc
      _ ≤ R * ((C₀ : ℝ) * ((Finset.Iic order).sup p₀) f) :=
        mul_le_mul_of_nonneg_left ((hSup f).trans (mul_le_mul_of_nonneg_left (hMono f) C₀.coe_nonneg)) hR
      _ = _ := (mul_assoc _ _ _).symm
  let L (z : ℂ) : 𝓓_{K}(X₀, ℝ) →L[ℝ] ℂ :=
    ⟨L₀ z, WithSeminorms.continuous_normedSpace_rng ℂ (ContDiffMapSupportedIn.withSeminorms ℝ X₀ ℝ ⊤ K)
      (L₀ z) ⟨Finset.Iic order, C, hUnif z⟩⟩
  refine ⟨p, order, C, C.coe_nonneg, L, ?_, fun f z _ => hUnif z f, ?_, ?_, ?_⟩
  · intro f
    apply ((hAnalytic f).const_mul c).congr
    intro z hz
    exact ite_eq_left hz
  · intro f z hz
    rw [← hQ f]
    exact hSeq z hz f
  · intro z hz f hoff
    let K' : Compacts X₀ := ⟨tsupport f, f.hasCompactSupport⟩
    let f' : 𝓓_{K'}(X₀, ℝ) := ContDiffMapSupportedIn.of_support_subset f.contDiff subset_closure
    let D' := fixedSupportShiftedField hW hb (K := K') (hoff.trans inter_subset_left)
    have hQ' : (Q f : X₀ → ℝ) = (D'^[p] f' : X₀ → ℝ) := by
      rw [hQ]
      have h₁ := ofSupportedIn_iterate_shiftedField hW hb hK le_rfl hK f p
      have h₂ := ofSupportedIn_iterate_shiftedField hW hb (hoff.trans inter_subset_left)
        le_rfl (hoff.trans inter_subset_left) f' p
      have h₀ : TestFunction.ofSupportedIn hK f =
          TestFunction.ofSupportedIn (hoff.trans inter_subset_left) f' := rfl
      exact congrArg (fun g : 𝓓(Ω, ℝ) => (g : X₀ → ℝ)) (h₁.trans ((congrArg _ h₀).trans h₂.symm))
    have hcut : cut f =ᶠ[atTop] fun _ => TestFunction.ofSupportedIn hoff (D'^[p] f') := by
      have h := puncturedCutoffSequence_eventuallyEq (hoff.trans inter_subset_left) hoff (D'^[p] f')
      have heq : cut f = puncturedCutoffSequence (hoff.trans inter_subset_left) (D'^[p] f') := by
        funext n
        ext x
        let χ : ContDiffBump (0 : N) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
        let k := χ (((n : ℝ) + 1) • x.2)
        change Q f x - k * Q f x = (D'^[p] f') x - k * (D'^[p] f') x
        rw [congrFun hQ' x]
      rw [heq]
      exact h
    have heval : T z (TestFunction.ofSupportedIn hoff (D'^[p] f')) = eigen ^ p *
        T z (TestFunction.ofSupportedIn hoff f') := by
      rw [ofSupportedIn_iterate_shiftedField hW hb (hoff.trans inter_subset_left) inter_subset_left hoff]
      exact eval_iterate_shiftedField (hW.mono inter_subset_left) (hb.mono inter_subset_left)
        (T z) eigen (hEig z hz) p _
    have hev : (fun n => c * T z (cut f n)) =ᶠ[atTop] fun _ => T z (TestFunction.ofSupportedIn hoff f') := by
      filter_upwards [hcut] with n hn
      rw [hn, heval, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ heigen), one_mul]
    exact tendsto_nhds_unique (hSeq z hz f) (tendsto_const_nhds.congr' hev.symm)

  · intro z hz T₀ hRestr hEig₀ C₀ hC₀ hBound₀ f
    have ht := (tendsto_eval_puncturedCutoffSequence hK T₀ hC₀ hBound₀ (Q f) (hflat f)).const_mul c
    have he : T₀ (TestFunction.ofSupportedIn hK (Q f)) =
        eigen ^ p * T₀ (TestFunction.ofSupportedIn hK f) := by
      rw [hQ, ofSupportedIn_iterate_shiftedField hW hb hK le_rfl hK f p]
      exact eval_iterate_shiftedField hW hb T₀ eigen hEig₀ p _
    rw [he, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ heigen), one_mul] at ht
    have ht' : Tendsto (fun n => c * T z (cut f n)) atTop (𝓝 (T₀ (TestFunction.ofSupportedIn hK f))) :=
      ht.congr fun n => (congrArg (c * ·) (hRestr (cut f n))).symm
    exact tendsto_nhds_unique (hSeq z hz f) ht'

/-- A uniform weighted bound gives a holomorphic eigen-distribution extension on a fixed compact. -/
def NormalEigenDistributionExtensionStatement : Prop :=
  ∀ (E : Type u) (N : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    (Ω : Opens (E × N)) (W : (E × N) → (E × N)) (b : (E × N) → ℝ)
    (hW : ContDiffOn ℝ ∞ W Ω) (hb : ContDiffOn ℝ ∞ b Ω)
    (K : Compacts (E × N)) (hK : (K : Set (E × N)) ⊆ Ω),
    (∀ x : E, (x, (0 : N)) ∈ Ω → W (x, 0) = 0 ∧ b (x, 0) = 0) →
    (∀ x : E, (x, (0 : N)) ∈ Ω → IsNilpotent (fderiv ℝ W (x, 0)).toLinearMap) →
    ∀ (S : Set ℂ), IsOpen S → ∀ (T : ℂ → 𝓓'(normalPuncturedDomain Ω, ℂ))
      (d m : ℕ) (A : ℝ), 0 ≤ A → (∀ z ∈ S, HasWeightedNormalBound (T z) K d m A) →
      (∀ g : 𝓓(normalPuncturedDomain Ω, ℝ), DifferentiableOn ℂ (fun z => T z g) S) →
      ∀ (eigen : ℂ), eigen ≠ 0 →
      (∀ z ∈ S, ∀ g, T z (shiftedVectorFieldDerivativeTest
        (hW.mono ((inter_subset_left) : (normalPuncturedDomain Ω : Set (E × N)) ⊆ Ω))
        (hb.mono inter_subset_left) g) = eigen * T z g) →
      ∃ p order : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∃ L : ℂ → 𝓓_{K}((E × N), ℝ) →L[ℝ] ℂ,
        (∀ f, DifferentiableOn ℂ (fun z => L z f) S) ∧
        (∀ f z, z ∈ S → ‖L z f‖ ≤ C * ContDiffMapSupportedIn.supSeminorm ℝ (E × N) ℝ ⊤ K order f) ∧
        (∀ f z, z ∈ S → Tendsto
          (fun n => (eigen ^ p)⁻¹ * T z (puncturedCutoffSequence hK
            ((fixedSupportShiftedField hW hb hK)^[p] f) n)) atTop (𝓝 (L z f))) ∧
        (∀ z ∈ S, ∀ (f : 𝓓_{K}((E × N), ℝ)) (hoff : tsupport f ⊆ normalPuncturedDomain Ω),
          L z f = T z ⟨f, f.contDiff, f.hasCompactSupport, hoff⟩) ∧
        ∀ z ∈ S, ∀ (T₀ : 𝓓'(Ω, ℂ)),
          (∀ g, T z g = T₀ (TestFunction.monoCLM ℝ g)) →
          (∀ g, T₀ (shiftedVectorFieldDerivativeTest hW hb g) = eigen * T₀ g) →
          ∀ C₀ : ℝ, 0 ≤ C₀ →
            (∀ f, ‖T₀ (TestFunction.ofSupportedIn hK f)‖ ≤ C₀ * ContDiffMapSupportedIn.supSeminorm ℝ (E × N) ℝ ⊤ K (d + m) f) →
            ∀ f, L z f = T₀ (TestFunction.ofSupportedIn hK f)

theorem normalEigenDistributionExtension : NormalEigenDistributionExtensionStatement.{u, v} := by
  intro E N _ _ _ _ _ _ Ω W b hW hb K hK hZero hNil S hS T d m A hA hT hHol eigen heigen hEig
  exact exists_fixedSupportNormalEigenExtension hW hb hK hZero hNil hS T hA hT hHol eigen heigen hEig

end Langlands.HarmonicAnalysis
