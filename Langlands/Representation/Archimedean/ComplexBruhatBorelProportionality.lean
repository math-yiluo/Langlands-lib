import Langlands.Analysis.DistributionFamilyIntegral
import Langlands.Representation.Archimedean.ComplexBruhatBorelOrbit
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar

/-! # Proportional covariant distributions on the longest complex Bruhat cell -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Function Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Distributions Topology Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.Whittaker Langlands.Analysis

universe uE uY uA

namespace ComplexBruhatBorel

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

variable (r : ℕ)

local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "U" => upperUnipotent (r + 1) ℂ
local notation "B" => upperTriangularSubgroup (r + 1) ℂ
local notation "P" => U × B
local notation "Cell" => longestBruhatCell ℂ r

attribute [local instance] matrixUnipotentBorelMulAction

/-- A product of fixed-space cutoffs with one translated factor gives a smooth
family with compact parameter support, by the compact transporter property. -/
private lemma smoothCompactFamily_mul_smul
    {E : Type uE} [NormedRing E] [NormedAlgebra ℝ E]
    {w v : Mat → E} (hw : ContDiff ℝ ∞ w) (hv : ContDiff ℝ ∞ v)
    {K L : Set Mat} (hK : IsCompact K) (hL : IsCompact L) (hKB : K ⊆ Cell) (hLB : L ⊆ Cell)
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
    have hU : Continuous (fun u : U => u.val.val) :=
      Units.continuous_val.comp continuous_subtype_val
    have hB : Continuous (fun b : B => b.val.val) :=
      Units.continuous_val.comp continuous_subtype_val
    exact hc.prodMk ((hU.comp (continuous_fst.comp e.continuous)).prodMk
      (hB.comp (continuous_snd.comp e.continuous).inv))
  have eqV (p : P) : (fun x => c p * (w x * v (e p • x))) = fun x => V (a p, x) := rfl
  obtain ⟨S, hS, hT⟩ := exists_compact_complexLongestBruhatBorel_transport r hK hL hKB hLB
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

private def testOfCompact {W : Opens Mat} {K : Compacts Mat} (hK : (K : Set Mat) ⊆ W)
    {v : Mat → ℂ} (hv : ContDiff ℝ ∞ v) (hv0 : ∀ x ∉ K, v x = 0) : 𝓓(W, ℂ) :=
  TestFunction.ofSupportedIn hK (ContDiffMapSupportedIn.of_support_subset hv
    (fun x hx => by by_contra h; exact hx (hv0 x h)))

/-- A compact subset of the cell admits a positive smooth window supported in the cell. -/
private lemma exists_window {K : Set Mat} (hK : IsCompact K) (hKC : K ⊆ Cell) :
    ∃ w : Mat → ℝ, ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧ tsupport w ⊆ Cell ∧
      (∀ x, 0 ≤ w x) ∧ (∀ x ∈ K, 0 < w x) := by
  obtain ⟨δ, hδ, hδC⟩ := hK.exists_cthickening_subset_open (Cell).isOpen hKC
  obtain ⟨w, hws, hw, hwI⟩ := (Metric.isOpen_thickening (δ := δ) (E := K)).exists_contDiff_support_eq
  have hwt : tsupport w ⊆ Metric.cthickening δ K := by
    rw [tsupport, hws]
    exact Metric.closure_thickening_subset_cthickening _ _
  have hwc : HasCompactSupport w := hK.cthickening.of_isClosed_subset isClosed_closure hwt
  have hnonneg (x : Mat) : 0 ≤ w x := (hwI (mem_range_self x)).1
  refine ⟨w, hw, hwc, hwt.trans hδC, hnonneg, fun x hx => ?_⟩
  have hx' : x ∈ support w := by rw [hws]; exact Metric.self_subset_thickening hδ K hx
  exact lt_of_le_of_ne (hnonneg x) (mem_support.mp hx').symm

private lemma exists_orbit_parameter {x : Mat} (hx : x ∈ Cell) :
    ∃ p : P, p • (weylLong (r + 1) ℂ).val = x := by
  let e := complexLongestBruhatBorelChart r
  refine ⟨e.symm ⟨x, hx⟩, ?_⟩
  rw [← complexLongestBruhatBorelChart_val, e.apply_symm_apply]

section Haar

variable [MeasurableSpace (upperUnipotent (r + 1) ℂ × upperTriangularSubgroup (r + 1) ℂ)]
  [BorelSpace (upperUnipotent (r + 1) ℂ × upperTriangularSubgroup (r + 1) ℂ)]
  (μ : Measure (upperUnipotent (r + 1) ℂ × upperTriangularSubgroup (r + 1) ℂ)) [μ.IsHaarMeasure]

/-- Character-weighted average along the product-group orbit in matrix space.
The formula uses the inverse of the parameter action. -/
private def orbitAverage (χ : P →* ℂ) (k : Mat → ℂ) (x : Mat) : ℂ :=
  ∫ p : P, χ p * k (p⁻¹ • x) ∂μ

local notation "β" => orbitAverage r μ

private lemma orbitAverage_smul
    (χ : P →* ℂ) (k : Mat → ℂ) (q : P) (x : Mat) :
    β χ k (q • x) = χ q * β χ k x := by
  let e := (Homeomorph.mulLeft q).toMeasurableEquiv
  have he : MeasurePreserving e μ μ := ⟨e.measurable, map_mul_left_eq_self μ q⟩
  unfold orbitAverage
  rw [← he.integral_comp' (fun p : P => χ p * k (p⁻¹ • (q • x))), ← integral_const_mul]
  apply integral_congr_ae (Eventually.of_forall fun p => ?_)
  change χ (q * p) * k ((q * p)⁻¹ • (q • x)) = χ q * (χ p * k (p⁻¹ • x))
  simp only [map_mul, mul_inv_rev, mul_smul, inv_smul_smul, mul_assoc]

variable [SecondCountableTopology (upperUnipotent (r + 1) ℂ × upperTriangularSubgroup (r + 1) ℂ)]

/-- Moving the group average through a distribution replaces the pointwise character
of the distribution by the same character in the orbit integral. -/
private lemma map_orbitAverage
    {W : Opens Mat} (hCW : Cell ≤ W) (χ : P →* ℂ) (hc : Continuous χ)
    (ρ k : 𝓓(Cell, ℂ)) (f : 𝓓(W, ℂ))
    (hf : ∀ x : Mat, f x = ∫ p : P, k x * ρ (p • x) ∂μ) :
    ∃ g : 𝓓(W, ℂ), (∀ x : Mat, g x = ρ x * orbitAverage r μ χ k x) ∧
      ∀ A : 𝓓(W, ℂ) →L[ℂ] ℂ,
        (∀ (p : P) (f g : 𝓓(W, ℂ)), (∀ x : Mat, g x = f (p • x)) → A g = χ p * A f) →
        A f = A g := by
  let K : Compacts Mat := ⟨tsupport k, k.hasCompactSupport⟩
  let L : Compacts Mat := ⟨tsupport ρ, ρ.hasCompactSupport⟩
  have k0 : ∀ x ∉ K, k x = 0 := fun _ h => image_eq_zero_of_notMem_tsupport h
  have ρ0 : ∀ x ∉ L, ρ x = 0 := fun _ h => image_eq_zero_of_notMem_tsupport h
  let Φ : P → Mat → ℂ := fun p x => k x * ρ (p • x)
  let Ψ : P → Mat → ℂ := fun p x => χ p * (ρ x * k (p⁻¹ • x))
  have hΦ : SmoothCompactFamily Φ := by
    simpa only [Homeomorph.refl_apply, id_eq, one_mul, Φ] using
      (smoothCompactFamily_mul_smul r k.contDiff ρ.contDiff K.isCompact L.isCompact
        k.tsupport_subset ρ.tsupport_subset k0 ρ0 (Homeomorph.refl P) (continuous_const (y := (1 : ℂ))))
  have hΨ : SmoothCompactFamily Ψ :=
    smoothCompactFamily_mul_smul r ρ.contDiff k.contDiff L.isCompact K.isCompact
      ρ.tsupport_subset k.tsupport_subset ρ0 k0 (Homeomorph.inv P) hc
  have hΦK : ∀ p, ∀ x ∉ K, Φ p x = 0 := fun p x hx => by simp [Φ, k0 x hx]
  have hΨL : ∀ p, ∀ x ∉ L, Ψ p x = 0 := fun p x hx => by simp [Ψ, ρ0 x hx]
  have hKW : (K : Set Mat) ⊆ W := k.tsupport_subset.trans hCW
  have hLW : (L : Set Mat) ⊆ W := ρ.tsupport_subset.trans hCW
  let φ : P → 𝓓(W, ℂ) := fun p => testOfCompact r hKW (hΦ.contDiff p) (hΦK p)
  let ψ : P → 𝓓(W, ℂ) := fun p => testOfCompact r hLW (hΨ.contDiff p) (hΨL p)
  have hs (p : P) : ContDiff ℝ ∞ (fun x : Mat => p • x) := by
    simp only [matrixUnipotentBorel_smul_def]
    exact (contDiff_const.mul contDiff_id).mul contDiff_const
  let η : P → 𝓓(W, ℂ) := fun p => testOfCompact r hLW
    (v := fun x => ρ x * k (p⁻¹ • x))
    (ρ.contDiff.mul (k.contDiff.comp (hs p⁻¹)))
    (fun x hx => by rw [ρ0 x hx, zero_mul])
  let g : 𝓓(W, ℂ) := testOfCompact r hLW (contDiff_integral_family (μ := μ) hΨ)
    (fun x hx => by simp [hΨL _ x hx])
  refine ⟨g, fun x => ?_, ?_⟩
  · change (∫ p : P, χ p * (ρ x * k (p⁻¹ • x)) ∂μ) =
      ρ x * (∫ p : P, χ p * k (p⁻¹ • x) ∂μ)
    rw [← integral_const_mul]
    apply integral_congr_ae (Eventually.of_forall fun p => ?_)
    ring
  · intro A hcov
    rw [map_integral_family (μ := μ) A hΦ hKW hΦK φ (fun _ _ => rfl) f hf,
      map_integral_family (μ := μ) A hΨ hLW hΨL ψ (fun _ _ => rfl) g (fun _ => rfl)]
    apply integral_congr_ae (Eventually.of_forall fun p => ?_)
    have heq : ψ p = χ p • η p := TestFunction.ext fun _ => rfl
    have hp : ∀ x : Mat, φ p x = η p (p • x) := by
      intro x
      change k x * ρ (p • x) = ρ (p • x) * k (p⁻¹ • (p • x))
      rw [inv_smul_smul, mul_comm]
    rw [hcov p (η p) (φ p) hp, heq, map_smul, smul_eq_mul]

private lemma exists_normalized_test {W : Opens Mat} (f : 𝓓(W, ℂ)) (hfC : tsupport f ⊆ Cell)
    (w : Mat → ℝ) (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w)
    (hws : tsupport w ⊆ Cell) (hw0 : ∀ x, 0 ≤ w x) (hwp : ∀ x ∈ tsupport f, 0 < w x) :
    ∃ k : 𝓓(Cell, ℂ), ∀ x : Mat, f x = ∫ p : P, k x * (w (p • x) : ℂ) ∂μ := by
  have wz : ∀ x ∉ tsupport w, w x = 0 := fun _ h => image_eq_zero_of_notMem_tsupport h
  have hFamily : SmoothCompactFamily (fun p : P => fun x : Mat => w x * w (p • x)) := by
    simpa only [Homeomorph.refl_apply, id_eq, one_mul] using
      (smoothCompactFamily_mul_smul r hw hw hwc hwc hws hws wz wz
        (Homeomorph.refl P) (continuous_const (y := (1 : ℝ))))
  let J : Mat → ℝ := fun x => ∫ p : P, w x * w (p • x) ∂μ
  have hJ : ContDiff ℝ ∞ J := contDiff_integral_family (μ := μ) hFamily
  have hJpos (x : Mat) (hx : x ∈ tsupport f) : 0 < J x := by
    obtain ⟨S, hS, hS0⟩ := hFamily.exists_compact
    apply integral_pos_of_integrable_nonneg_nonzero (x := (1 : P))
      (hFamily.continuous.comp (continuous_id.prodMk continuous_const))
      (integrable_family_of_compact μ hFamily.continuous hS hS0 x)
      (fun p => mul_nonneg (hw0 x) (hw0 (p • x)))
    change w x * w ((1 : P) • x) ≠ 0
    rw [one_smul]
    exact (mul_pos (hwp x hx) (hwp x hx)).ne'
  let K : Compacts Mat := ⟨tsupport f, f.hasCompactSupport⟩
  let k : Mat → ℂ := fun x => (w x : ℂ) * (f x / (J x : ℂ))
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
        (Complex.ofRealCLM.contDiff.comp hw).contDiffAt.mul (f.contDiff.contDiffAt.mul hjinv)
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
      exact hk0 y hy
  refine ⟨testOfCompact r (K := K) hfC hk hk0, fun x => ?_⟩
  change f x = ∫ p : P, k x * (w (p • x) : ℂ) ∂μ
  by_cases hx : x ∈ K
  · symm
    calc
      (∫ p : P, k x * (w (p • x) : ℂ) ∂μ) =
          ∫ p : P, (f x / (J x : ℂ)) * ((w x * w (p • x) : ℝ) : ℂ) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        change k x * (w (p • x) : ℂ) = (f x / (J x : ℂ)) * ((w x * w (p • x) : ℝ) : ℂ)
        rw [Complex.ofReal_mul]
        dsimp only [k]
        ring
      _ = (f x / (J x : ℂ)) * (J x : ℂ) := by rw [integral_const_mul, integral_complex_ofReal]
      _ = f x := div_mul_cancel₀ _ (hJN x hx)
  · rw [hk0 x hx, image_eq_zero_of_notMem_tsupport hx]
    simp

end Haar

end ComplexBruhatBorel

open ComplexBruhatBorel

local notation "Mat" r => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "P" r => upperUnipotent (r + 1) ℂ × upperTriangularSubgroup (r + 1) ℂ
local notation "Cell" r => longestBruhatCell ℂ r

attribute [local instance] matrixUnipotentBorelMulAction

/-- The distributions have the same covariance under the unipotent and Borel group action.
The first distribution is nonzero on some test supported in the longest cell. -/
def ComplexBruhatBorelProportionalityStatement : Prop :=
  ∀ (r : ℕ) [SecondCountableTopology (P r)] [MeasurableSpace (P r)] [BorelSpace (P r)]
    (μ : Measure (P r)) [μ.IsHaarMeasure] {W : Opens (Mat r)}, (Cell r) ≤ W →
  ∀ (χ : (P r) →* ℂ), Continuous χ →
  ∀ (A₀ A₁ : 𝓓(W, ℂ) →L[ℂ] ℂ),
    (∀ (p : (P r)) (f g : 𝓓(W, ℂ)), (∀ x : (Mat r), g x = f (p • x)) → A₀ g = χ p * A₀ f) →
    (∀ (p : (P r)) (f g : 𝓓(W, ℂ)), (∀ x : (Mat r), g x = f (p • x)) → A₁ g = χ p * A₁ f) →
    (∃ f : 𝓓(W, ℂ), tsupport f ⊆ (Cell r) ∧ A₀ f ≠ 0) →
    ∃ c : ℂ, ∀ f : 𝓓(W, ℂ), tsupport f ⊆ (Cell r) → A₁ f = c * A₀ f

theorem complexBruhatBorelProportionality : ComplexBruhatBorelProportionalityStatement := by
  intro r _ _ _ μ _ W hCW χ hχ A₀ A₁ hCov₀ hCov₁ hNonzero
  obtain ⟨f₀, hf₀, hA₀⟩ := hNonzero
  refine ⟨A₁ f₀ / A₀ f₀, fun f hf => ?_⟩
  obtain ⟨w, hw, hwc, hws, hw0, hwp⟩ :=
    exists_window r (f₀.hasCompactSupport.union f.hasCompactSupport) (union_subset hf₀ hf)
  let ρ : 𝓓((Cell r), ℂ) := testOfCompact r (K := ⟨tsupport w, hwc⟩) hws
    (Complex.ofRealCLM.contDiff.comp hw)
    (fun x hx => by simp [image_eq_zero_of_notMem_tsupport (f := w) hx])
  obtain ⟨k₀, hk₀⟩ := exists_normalized_test r μ f₀ hf₀ w hw hwc hws hw0
    (fun x hx => hwp x (.inl hx))
  obtain ⟨k, hk⟩ := exists_normalized_test r μ f hf w hw hwc hws hw0
    (fun x hx => hwp x (.inr hx))
  obtain ⟨g₀, hg₀, hRef⟩ := map_orbitAverage r μ hCW χ hχ ρ k₀ f₀ hk₀
  obtain ⟨g, hg, hTransfer⟩ := map_orbitAverage r μ hCW χ hχ ρ k f hk
  let y : (Mat r) := (weylLong (r + 1) ℂ).val
  have hnonzero : orbitAverage r μ χ k₀ y ≠ 0 := by
    intro h
    apply hA₀
    have heq : g₀ = 0 := by
      apply TestFunction.ext
      intro x
      change g₀ x = 0
      rw [hg₀ x]
      by_cases hx : x ∈ (Cell r)
      · obtain ⟨p, hp⟩ := exists_orbit_parameter r hx
        rw [← hp, orbitAverage_smul, h, mul_zero, mul_zero]
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (ρ.tsupport_subset h)), zero_mul]
    rw [hRef A₀ hCov₀, heq, map_zero]
  let z := orbitAverage r μ χ k y / orbitAverage r μ χ k₀ y
  have hscale : g = z • g₀ := by
    apply TestFunction.ext
    intro x
    change g x = z * g₀ x
    rw [hg x, hg₀ x]
    by_cases hx : x ∈ (Cell r)
    · obtain ⟨p, hp⟩ := exists_orbit_parameter r hx
      change p • y = x at hp
      rw [← hp, orbitAverage_smul, orbitAverage_smul]
      dsimp only [z]
      field_simp [hnonzero]
    · rw [image_eq_zero_of_notMem_tsupport (f := ρ) (fun h => hx (ρ.tsupport_subset h)),
        zero_mul, zero_mul, mul_zero]
  have hA₀f : A₀ f = z * A₀ f₀ := by
    rw [hTransfer A₀ hCov₀, hscale, map_smul, smul_eq_mul, ← hRef A₀ hCov₀]
  have hA₁f : A₁ f = z * A₁ f₀ := by
    rw [hTransfer A₁ hCov₁, hscale, map_smul, smul_eq_mul, ← hRef A₁ hCov₁]
  rw [hA₀f, hA₁f]
  field_simp [hA₀]

end Langlands.Archimedean
