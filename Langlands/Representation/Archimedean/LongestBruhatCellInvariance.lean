import Langlands.Analysis.DistributionFamilyIntegral
import Langlands.Representation.Archimedean.LongestBruhatCell
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar

/-! # Weyl-transpose invariance on the longest Bruhat cell -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Function Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Distributions Topology Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.Whittaker Langlands.Analysis

universe uF uE uY uA

/-- Spatial derivatives of the slices of a jointly smooth function are jointly continuous. -/
private lemma continuous_iteratedFDeriv_slice
    {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Y × A → E} (hf : ContDiff ℝ ∞ f) (i : ℕ) :
    Continuous (fun z : Y × A => iteratedFDeriv ℝ i (fun x : A => f (z.1, x)) z.2) := by
  let l := ContinuousLinearMap.inr ℝ Y A
  let L : (Y × A [×i]→L[ℝ] E) →L[ℝ] (A [×i]→L[ℝ] E) :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => l)
  have hEq (z : Y × A) : iteratedFDeriv ℝ i (fun x : A => f (z.1, x)) z.2 =
      L (iteratedFDeriv ℝ i f z) := by
    let g : Y × A → E := fun y => f ((z.1, 0) + y)
    have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add contDiff_id)
    have he : (fun x : A => f (z.1, x)) = g ∘ l := by
      funext x
      simp [g, l]
    rw [he, l.iteratedFDeriv_comp_right hg _ (by simp),
      show iteratedFDeriv ℝ i g (l z.2) = iteratedFDeriv ℝ i f ((z.1, 0) + l z.2) from
        iteratedFDeriv_comp_add_left i _ _]
    simp [l, L]
  simp only [hEq]
  exact L.continuous.comp (hf.continuous_iteratedFDeriv (m := i) (by simp))

variable (F : Type uF) [RCLike F] (n : ℕ)
local notation "Mat" => Matrix (Fin (n + 1)) (Fin (n + 1)) F
local notation "GL" => Langlands.GeneralLinear (n + 1) F
local notation "U" => upperUnipotent (n + 1) F
local notation "P" => U × U
local notation "B" => longestBruhatCell F n
local notation "τ" => matrixWeylTranspose F n
local notation "σ" => matrixUnipotentPairTranspose F n

attribute [local instance] matrixUnipotentPairMulAction

/-- A product of fixed-space cutoffs with one translated factor gives a smooth
family with compact parameter support, by the compact transporter property. -/
private lemma smoothCompactFamily_mul_smul
    {E : Type uE} [NormedRing E] [NormedAlgebra ℝ E]
    {w v : Mat → E} (hw : ContDiff ℝ ∞ w) (hv : ContDiff ℝ ∞ v)
    {K L : Set Mat} (hK : IsCompact K) (hL : IsCompact L) (hKB : K ⊆ B) (hLB : L ⊆ B)
    (hw0 : ∀ x ∉ K, w x = 0) (hv0 : ∀ x ∉ L, v x = 0)
    (e : P ≃ₜ P) {c : P → E} (hc : Continuous c) :
    SmoothCompactFamily (fun p x => c p * (w x * v (e p • x))) := by
  let V : (E × Mat × Mat) × Mat → E := fun z =>
    z.1.1 * (w z.2 * v (z.1.2.1 * z.2 * z.1.2.2))
  have hV : ContDiff ℝ ∞ V := by
    dsimp [V]
    fun_prop
  let a : P → E × Mat × Mat := fun p => (c p, (e p).1.val.val, ((e p).2⁻¹).val.val)
  have ha : Continuous a := by
    have hval : Continuous (fun u : U => u.val.val) :=
      Units.continuous_val.comp continuous_subtype_val
    exact hc.prodMk ((hval.comp (continuous_fst.comp e.continuous)).prodMk
      (hval.comp (continuous_snd.comp e.continuous).inv))
  have eqV (p : P) : (fun x => c p * (w x * v (e p • x))) = fun x => V (a p, x) := rfl
  obtain ⟨S, hS, hT⟩ := exists_compact_longestBruhatCell_transport F n hK hL hKB hLB
  refine ⟨fun p => ?_, fun i => ?_, ⟨e ⁻¹' S, (e.isCompact_preimage).mpr hS, ?_⟩⟩
  · rw [eqV]
    exact hV.comp (contDiff_const.prodMk contDiff_id)
  · simp only [eqV]
    exact (continuous_iteratedFDeriv_slice hV i).comp ((ha.comp continuous_fst).prodMk continuous_snd)
  · intro p hp x
    by_cases hx : x ∈ K
    · have hx' : e p • x ∉ L := fun h => hp (hT (e p) x hx h)
      rw [hv0 _ hx', mul_zero, mul_zero]
    · rw [hw0 _ hx, zero_mul, mul_zero]

private def pairTransposeMulEquiv : P ≃ₜ* P where
  toHomeomorph := σ
  map_mul' := matrixUnipotentPairTranspose_mul F n

private lemma pairTranspose_inv (p : P) : σ p⁻¹ = (σ p)⁻¹ :=
  map_inv (pairTransposeMulEquiv F n) p

/-- An involutive continuous automorphism preserves left Haar measure. -/
private lemma measurePreserving_involution_of_isHaarMeasure
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (e : G ≃ₜ* G) (he : Function.Involutive e)
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    MeasurePreserving e.toHomeomorph.toMeasurableEquiv μ μ := by
  have hee : e.trans e = ContinuousMulEquiv.refl G := by
    ext x
    exact he x
  have hs : mulEquivHaarChar e * mulEquivHaarChar e = 1 := by
    rw [← mulEquivHaarChar_trans, hee, mulEquivHaarChar_refl]
  have h1 : mulEquivHaarChar e = 1 :=
    (mul_self_inj (show 0 ≤ mulEquivHaarChar e from bot_le) (show 0 ≤ 1 from bot_le)).mp
      (hs.trans (one_mul 1).symm)
  have hm := mulEquivHaarChar_smul_map μ e
  rw [h1, one_smul] at hm
  exact ⟨e.toHomeomorph.toMeasurableEquiv.measurable, hm⟩

section Average

variable [MeasurableSpace (upperUnipotent (n + 1) F × upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F × upperUnipotent (n + 1) F)]
  (μ : Measure (upperUnipotent (n + 1) F × upperUnipotent (n + 1) F))

/-- Character-weighted average along the product-group orbit in matrix space.
The formula uses the inverse of the parameter action. -/
def longestBruhatFiberAverage (χ : P →* ℂ) (k : Mat → ℂ) (x : Mat) : ℂ :=
  ∫ p : P, χ p * k (p⁻¹ • x) ∂μ

local notation "β" => longestBruhatFiberAverage F n μ

private lemma fiberAverage_smul [μ.IsMulLeftInvariant]
    (χ : P →* ℂ) (k : Mat → ℂ) (q : P) (x : Mat) :
    β χ k (q • x) = χ q * β χ k x := by
  let e := (Homeomorph.mulLeft q).toMeasurableEquiv
  have he : MeasurePreserving e μ μ := ⟨e.measurable, map_mul_left_eq_self μ q⟩
  unfold longestBruhatFiberAverage
  rw [← he.integral_comp' (fun p : P => χ p * k (p⁻¹ • (q • x))), ← integral_const_mul]
  apply integral_congr_ae (Eventually.of_forall fun p => ?_)
  change χ (q * p) * k ((q * p)⁻¹ • (q • x)) = χ q * (χ p * k (p⁻¹ • x))
  simp only [map_mul, mul_inv_rev, mul_smul, inv_smul_smul, mul_assoc]

private lemma fiberAverage_transpose
    (hμ : MeasurePreserving (σ).toMeasurableEquiv μ μ)
    (χ : P →* ℂ) (hχ : ∀ p, χ (σ p) = χ p) (k : Mat → ℂ) (x : Mat) :
    β χ (k ∘ τ) x = β χ k (τ x) := by
  unfold longestBruhatFiberAverage
  rw [← hμ.integral_comp' (fun p : P => χ p * k (p⁻¹ • τ x))]
  apply integral_congr_ae (Eventually.of_forall fun p => ?_)
  change χ p * k (τ (p⁻¹ • x)) = χ (σ p) * k ((σ p)⁻¹ • τ x)
  rw [matrixWeylTranspose_smul, pairTranspose_inv, hχ]

private lemma fiberAverage_transpose_of_mem [μ.IsMulLeftInvariant]
    (hμ : MeasurePreserving (σ).toMeasurableEquiv μ μ)
    (χ : P →* ℂ) (hχ : ∀ p, χ (σ p) = χ p) (k : Mat → ℂ) {x : Mat} (hx : x ∈ B) :
    β χ (k ∘ τ) x = β χ k x := by
  rw [fiberAverage_transpose F n μ hμ χ hχ]
  obtain ⟨p, y, _, hy, rfl⟩ := exists_smul_fixed_of_mem_longestBruhatCell F n hx
  rw [matrixWeylTranspose_smul, hy, fiberAverage_smul, fiberAverage_smul, hχ]

end Average

private def testOfCompact {W : Opens Mat} {K : Compacts Mat} (hK : (K : Set Mat) ⊆ W)
    {v : Mat → ℂ} (hv : ContDiff ℝ ∞ v) (hv0 : ∀ x ∉ K, v x = 0) : 𝓓(W, ℂ) :=
  TestFunction.ofSupportedIn hK (ContDiffMapSupportedIn.of_support_subset hv
    (fun x hx => by by_contra h; exact hx (hv0 x h)))

section Transfer

variable [SecondCountableTopology (upperUnipotent (n + 1) F × upperUnipotent (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F × upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F × upperUnipotent (n + 1) F)]
  (μ : Measure (upperUnipotent (n + 1) F × upperUnipotent (n + 1) F)) [IsFiniteMeasureOnCompacts μ]

/-- Moving the group average through a distribution replaces the pointwise character
of the distribution by the same character in the orbit integral. -/
private lemma map_longestBruhatFiberAverage
    {W : Opens Mat} (hBW : B ≤ W) (A : 𝓓(W, ℂ) →L[ℂ] ℂ) (χ : P →* ℂ) (hc : Continuous χ)
    (hcov : ∀ (p : P) (f g : 𝓓(W, ℂ)), (∀ x : Mat, g x = f (p • x)) →
      A g = χ p * A f)
    (ρ k : 𝓓(B, ℂ)) (f : 𝓓(W, ℂ))
    (hf : ∀ x : Mat, f x = ∫ p : P, k x * ρ (p • x) ∂μ) :
    ∃ g : 𝓓(W, ℂ), (∀ x : Mat, g x = ρ x * longestBruhatFiberAverage F n μ χ k x) ∧
      A f = A g := by
  let K : Compacts Mat := ⟨tsupport k, k.hasCompactSupport⟩
  let L : Compacts Mat := ⟨tsupport ρ, ρ.hasCompactSupport⟩
  have k0 : ∀ x ∉ K, k x = 0 := fun _ h => image_eq_zero_of_notMem_tsupport h
  have ρ0 : ∀ x ∉ L, ρ x = 0 := fun _ h => image_eq_zero_of_notMem_tsupport h
  let Φ : P → Mat → ℂ := fun p x => k x * ρ (p • x)
  let Ψ : P → Mat → ℂ := fun p x => χ p * (ρ x * k (p⁻¹ • x))
  have hΦ : SmoothCompactFamily Φ := by
    simpa only [Homeomorph.refl_apply, id_eq, one_mul, Φ] using
      (smoothCompactFamily_mul_smul F n k.contDiff ρ.contDiff K.isCompact L.isCompact
        k.tsupport_subset ρ.tsupport_subset k0 ρ0 (Homeomorph.refl P) (continuous_const (y := (1 : ℂ))))
  have hΨ : SmoothCompactFamily Ψ :=
    smoothCompactFamily_mul_smul F n ρ.contDiff k.contDiff L.isCompact K.isCompact
      ρ.tsupport_subset k.tsupport_subset ρ0 k0 (Homeomorph.inv P) hc
  have hΦK : ∀ p, ∀ x ∉ K, Φ p x = 0 := fun p x hx => by simp [Φ, k0 x hx]
  have hΨL : ∀ p, ∀ x ∉ L, Ψ p x = 0 := fun p x hx => by simp [Ψ, ρ0 x hx]
  have hKW : (K : Set Mat) ⊆ W := k.tsupport_subset.trans hBW
  have hLW : (L : Set Mat) ⊆ W := ρ.tsupport_subset.trans hBW
  let φ : P → 𝓓(W, ℂ) := fun p => testOfCompact F n hKW (hΦ.contDiff p) (hΦK p)
  let ψ : P → 𝓓(W, ℂ) := fun p => testOfCompact F n hLW (hΨ.contDiff p) (hΨL p)
  have hs (p : P) : ContDiff ℝ ∞ (fun x : Mat => p • x) := by
    simp only [matrixUnipotentPair_smul_def]
    exact (contDiff_const.mul contDiff_id).mul contDiff_const
  let η : P → 𝓓(W, ℂ) := fun p => testOfCompact F n hLW
    (v := fun x => ρ x * k (p⁻¹ • x))
    (ρ.contDiff.mul (k.contDiff.comp (hs p⁻¹)))
    (fun x hx => by rw [ρ0 x hx, zero_mul])
  let g : 𝓓(W, ℂ) := testOfCompact F n hLW (contDiff_integral_family (μ := μ) hΨ)
    (fun x hx => by simp [hΨL _ x hx])
  refine ⟨g, fun x => ?_, ?_⟩
  · change (∫ p : P, χ p * (ρ x * k (p⁻¹ • x)) ∂μ) =
      ρ x * (∫ p : P, χ p * k (p⁻¹ • x) ∂μ)
    rw [← integral_const_mul]
    apply integral_congr_ae (Eventually.of_forall fun p => ?_)
    ring
  · rw [map_integral_family (μ := μ) A hΦ hKW hΦK φ (fun _ _ => rfl) f hf,
      map_integral_family (μ := μ) A hΨ hLW hΨL ψ (fun _ _ => rfl) g (fun _ => rfl)]
    apply integral_congr_ae (Eventually.of_forall fun p => ?_)
    have heq : ψ p = χ p • η p := TestFunction.ext fun _ => rfl
    have hp : ∀ x : Mat, φ p x = η p (p • x) := by
      intro x
      change k x * ρ (p • x) = ρ (p • x) * k (p⁻¹ • (p • x))
      rw [inv_smul_smul, mul_comm]
    rw [hcov p (η p) (φ p) hp, heq, map_smul, smul_eq_mul]

end Transfer

/-- A compact subset of the cell admits a nonnegative, transpose-invariant, smooth
cutoff that is strictly positive on the subset and compactly supported in the cell. -/
private lemma exists_transpose_cutoff {K : Set Mat} (hK : IsCompact K) (hKB : K ⊆ B) :
    ∃ r : Mat → ℝ, ContDiff ℝ ∞ r ∧ HasCompactSupport r ∧ tsupport r ⊆ B ∧
      (∀ x, 0 ≤ r x) ∧ (∀ x ∈ K, 0 < r x) ∧ (∀ x, r (τ x) = r x) := by
  obtain ⟨δ, hδ, hδB⟩ := hK.exists_cthickening_subset_open (B).isOpen hKB
  obtain ⟨v, hV, hv, hvI⟩ := (Metric.isOpen_thickening (δ := δ) (E := K)).exists_contDiff_support_eq
  have hvs : tsupport v ⊆ Metric.cthickening δ K := by
    rw [tsupport, hV]
    exact Metric.closure_thickening_subset_cthickening _ _
  have hvc : HasCompactSupport v := hK.cthickening.of_isClosed_subset isClosed_closure hvs
  have hvn (x : Mat) : 0 ≤ v x := (hvI (mem_range_self x)).1
  have hvp (x : Mat) (hx : x ∈ K) : 0 < v x := by
    have h : x ∈ support v := by rw [hV]; exact Metric.self_subset_thickening hδ K hx
    exact lt_of_le_of_ne (hvn x) (mem_support.mp h).symm
  have hτc : HasCompactSupport (v ∘ τ) :=
    (((τ).toHomeomorph.isCompact_preimage).mpr hvc).of_isClosed_subset isClosed_closure
      (tsupport_comp_subset_preimage v (τ).continuous)
  have hτB : tsupport (v ∘ τ) ⊆ B := fun x hx =>
    (matrixWeylTranspose_mem_longestBruhatCell_iff F n x).mp
      (hδB (hvs (tsupport_comp_subset_preimage v (τ).continuous hx)))
  refine ⟨fun x => v x + v (τ x), hv.add (hv.comp (τ).contDiff), hvc.add hτc,
    (tsupport_add v (v ∘ τ)).trans (union_subset (hvs.trans hδB) hτB),
    fun x => add_nonneg (hvn x) (hvn (τ x)),
    fun x hx => add_pos_of_pos_of_nonneg (hvp x hx) (hvn (τ x)), fun x => ?_⟩
  change v (τ x) + v (τ (τ x)) = v x + v (τ x)
  rw [matrixWeylTranspose_involutive F n x, add_comm]

section Normalize

variable [SecondCountableTopology (upperUnipotent (n + 1) F × upperUnipotent (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F × upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F × upperUnipotent (n + 1) F)]
  (μ : Measure (upperUnipotent (n + 1) F × upperUnipotent (n + 1) F)) [μ.IsHaarMeasure]

/-- Express a test function supported in the longest cell as a compact-family average
against a transpose-invariant cutoff. -/
private lemma exists_normalized_longestBruhatTest {W : Opens Mat} (f : 𝓓(W, ℂ))
    (hfB : tsupport f ⊆ B) :
    ∃ ρ k : 𝓓(B, ℂ), (∀ x : Mat, ρ (τ x) = ρ x) ∧
      (∀ x : Mat, f x = ∫ p : P, k x * ρ (p • x) ∂μ) := by
  obtain ⟨r, hr, hrc, hrs, hr0, hrp, hrτ⟩ := exists_transpose_cutoff F n f.hasCompactSupport hfB
  have rz : ∀ x ∉ tsupport r, r x = 0 := fun _ h => image_eq_zero_of_notMem_tsupport h
  have hrF : SmoothCompactFamily (fun p : P => fun x : Mat => r x * r (p • x)) := by
    simpa only [Homeomorph.refl_apply, id_eq, one_mul] using
      (smoothCompactFamily_mul_smul F n hr hr hrc hrc hrs hrs rz rz
        (Homeomorph.refl P) (continuous_const (y := (1 : ℝ))))
  let J : Mat → ℝ := fun x => ∫ p : P, r x * r (p • x) ∂μ
  have hJ : ContDiff ℝ ∞ J := contDiff_integral_family (μ := μ) hrF
  have hJpos (x : Mat) (hx : x ∈ tsupport f) : 0 < J x := by
    obtain ⟨S, hS, hS0⟩ := hrF.exists_compact
    apply integral_pos_of_integrable_nonneg_nonzero (x := (1 : P))
      (hrF.continuous.comp (continuous_id.prodMk continuous_const))
      (integrable_family_of_compact μ hrF.continuous hS hS0 x)
      (fun p => mul_nonneg (hr0 x) (hr0 (p • x)))
    change r x * r ((1 : P) • x) ≠ 0
    rw [one_smul]
    exact (mul_pos (hrp x hx) (hrp x hx)).ne'
  let K : Compacts Mat := ⟨tsupport f, f.hasCompactSupport⟩
  let L : Compacts Mat := ⟨tsupport r, hrc⟩
  let ρ : 𝓓(B, ℂ) := testOfCompact F n (K := L) hrs (Complex.ofRealCLM.contDiff.comp hr)
    (fun x hx => by simp [rz x hx])
  let k : Mat → ℂ := fun x => (r x : ℂ) * (f x / (J x : ℂ))
  have hJN (x : Mat) (hx : x ∈ tsupport f) : (J x : ℂ) ≠ 0 := by
    exact_mod_cast (hJpos x hx).ne'
  have hk0 (x : Mat) (hx : x ∉ K) : k x = 0 := by
    dsimp [k]
    rw [image_eq_zero_of_notMem_tsupport hx, zero_div, mul_zero]
  have hk : ContDiff ℝ ∞ k := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport f
    · have hjc : ContDiff ℝ ∞ (fun y : Mat => (J y : ℂ)) := Complex.ofRealCLM.contDiff.comp hJ
      have hjinv := hjc.contDiffAt.inv (x := x) (hJN x hx)
      simpa only [k, div_eq_mul_inv, Pi.inv_apply, Function.comp_apply, Complex.ofRealCLM_apply] using
        (Complex.ofRealCLM.contDiff.comp hr).contDiffAt.mul (f.contDiff.contDiffAt.mul hjinv)
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
      exact hk0 y hy
  refine ⟨ρ, testOfCompact F n (K := K) hfB hk hk0, fun x => ?_, fun x => ?_⟩
  · change (r (τ x) : ℂ) = (r x : ℂ)
    rw [hrτ]
  · change f x = ∫ p : P, k x * (r (p • x) : ℂ) ∂μ
    by_cases hx : x ∈ K
    · symm
      calc
        (∫ p : P, k x * (r (p • x) : ℂ) ∂μ) =
            ∫ p : P, (f x / (J x : ℂ)) * ((r x * r (p • x) : ℝ) : ℂ) ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun p => ?_)
          change k x * (r (p • x) : ℂ) = (f x / (J x : ℂ)) * ((r x * r (p • x) : ℝ) : ℂ)
          rw [Complex.ofReal_mul]
          dsimp only [k]
          ring
        _ = (f x / (J x : ℂ)) * (J x : ℂ) := by rw [integral_const_mul, integral_complex_ofReal]
        _ = f x := div_mul_cancel₀ _ (hJN x hx)
    · rw [hk0 x hx, image_eq_zero_of_notMem_tsupport hx]
      simp

end Normalize

/-- **Open-cell step of Shalika's distribution argument.** A distribution on a matrix
open set containing the longest Bruhat cell is invariant on tests supported in that
cell if it is covariant under the product unipotent group for a continuous character
preserved by the transpose automorphism of the product. -/
theorem longestBruhatCell_transpose_invariant_of_covariant {W : Opens Mat} (hBW : B ≤ W)
    (A : 𝓓(W, ℂ) →L[ℂ] ℂ) (χ : P →* ℂ) (hc : Continuous χ)
    (hχ : ∀ p, χ (σ p) = χ p)
    (hcov : ∀ (p : P) (f g : 𝓓(W, ℂ)), (∀ x : Mat, g x = f (p • x)) →
      A g = χ p * A f)
    (f g : 𝓓(W, ℂ)) (hfB : tsupport f ⊆ B) (hg : ∀ x : Mat, g x = f (τ x)) :
    A g = A f := by
  let : LocallyCompactSpace GL := (Units.isOpenEmbedding_val (R := Mat)).locallyCompactSpace
  let : LocallyCompactSpace U := UpperUnipotent.locallyCompactSpace
  let : SecondCountableTopology GL :=
    (Units.isOpenEmbedding_val (R := Mat)).isEmbedding.secondCountableTopology
  let : SecondCountableTopology U := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : MeasurableSpace P := borel P
  let : BorelSpace P := ⟨rfl⟩
  let μ : Measure P := Measure.haar
  have : μ.IsHaarMeasure := by dsimp [μ]; infer_instance
  have : μ.Regular := by dsimp [μ, Measure.haar]; infer_instance
  have hμ : MeasurePreserving (σ).toMeasurableEquiv μ μ :=
    measurePreserving_involution_of_isHaarMeasure (pairTransposeMulEquiv F n)
      (matrixUnipotentPairTranspose_involutive F n) μ
  obtain ⟨ρ, k, hρτ, hf⟩ := exists_normalized_longestBruhatTest F n μ f hfB
  let J : Compacts Mat := ⟨τ ⁻¹' tsupport k,
    ((τ).toHomeomorph.isCompact_preimage).mpr k.hasCompactSupport⟩
  have hJB : (J : Set Mat) ⊆ B := fun x hx =>
    (matrixWeylTranspose_mem_longestBruhatCell_iff F n x).mp (k.tsupport_subset hx)
  let k' : 𝓓(B, ℂ) := testOfCompact F n hJB (v := k ∘ τ) (k.contDiff.comp (τ).contDiff)
    (fun x hx => show k (τ x) = 0 from image_eq_zero_of_notMem_tsupport hx)
  have hg' (x : Mat) : g x = ∫ p : P, k' x * ρ (p • x) ∂μ := by
    rw [hg, hf, ← hμ.integral_comp' (fun p : P => k' x * ρ (p • x))]
    apply integral_congr_ae (Eventually.of_forall fun p => ?_)
    change k (τ x) * ρ (p • τ x) = k (τ x) * ρ (σ p • x)
    have ht := matrixWeylTranspose_smul F n p (τ x)
    rw [matrixWeylTranspose_involutive F n x] at ht
    rw [← ht, hρτ]
  obtain ⟨a, ha, heqa⟩ := map_longestBruhatFiberAverage F n μ hBW A χ hc hcov ρ k f hf
  obtain ⟨b, hb, heqb⟩ := map_longestBruhatFiberAverage F n μ hBW A χ hc hcov ρ k' g hg'
  rw [heqa, heqb]
  congr 1
  apply TestFunction.ext
  intro x
  rw [hb, ha]
  by_cases hx : x ∈ B
  · rw [show (k' : Mat → ℂ) = (k : Mat → ℂ) ∘ τ from rfl,
      fiberAverage_transpose_of_mem F n μ hμ χ hχ k hx]
  · rw [ρ.zero_on_compl hx]
    simp

/-- Open-cell invariance in the two-sided matrix convention `x ↦ u x v`, with the
same transpose-stable unipotent character on each factor. -/
theorem longestBruhatCell_transpose_invariant {W : Opens Mat} (hBW : B ≤ W)
    (A : 𝓓(W, ℂ) →L[ℂ] ℂ) (χ : U →* ℂ) (hc : Continuous χ)
    (hχ : ∀ u, χ (weylTransposeUnipotent n F u) = χ u)
    (hcov : ∀ (u v : U) (f g : 𝓓(W, ℂ)), (∀ x : Mat, g x = f (u.val.val * x * v.val.val)) →
      A g = (χ u * χ v) * A f)
    (f g : 𝓓(W, ℂ)) (hfB : tsupport f ⊆ B) (hg : ∀ x : Mat, g x = f (τ x)) :
    A g = A f := by
  let χ' : P →* ℂ := {
    toFun p := χ p.1 * χ p.2⁻¹
    map_one' := by simp
    map_mul' := fun p q => by
      change χ (p.1 * q.1) * χ (p.2 * q.2)⁻¹ = (χ p.1 * χ p.2⁻¹) * (χ q.1 * χ q.2⁻¹)
      simp only [mul_inv_rev, map_mul]
      ring }
  refine longestBruhatCell_transpose_invariant_of_covariant F n hBW A χ'
    ((hc.comp continuous_fst).mul (hc.comp continuous_snd.inv)) ?_ ?_ f g hfB hg
  · intro p
    change χ (σ p).1 * χ ((σ p).2)⁻¹ = χ p.1 * χ p.2⁻¹
    simp only [matrixUnipotentPairTranspose_apply, ← matrixWeylTranspose_unipotent_inv,
      inv_inv, hχ, mul_comm]
  · intro p f₀ g₀ h
    exact hcov p.1 p.2⁻¹ f₀ g₀ h

end Langlands.Archimedean
