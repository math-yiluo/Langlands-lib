import Langlands.Analysis.SeveralComplex.MovingRootDivision
import Langlands.Global.RankinSelberg.OrdinarySemilocalNormalization
import Langlands.Global.RankinSelberg.RealOverlappingNormalization
import Langlands.Global.RankinSelberg.RealPositionPairPolynomial

/-! # Normalization by the real block factors in a holomorphic family -/

noncomputable section

open Filter Metric Set
open scoped NNReal Topology

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealBlockParameters

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean Langlands.Analysis.SeveralComplex
open RealPrincipalSeries (expand)
open RealJacquet (ContinuationPackage realOverlappingNormalization)

private theorem prod_map_div_const (l : List ℂ) (c : ℂ) :
    (l.map fun z => z / c).prod = l.prod / c ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, ih, mul_div_mul_comm, pow_succ']

private def pairRoots {n m : ℕ} (shifts : Shape → Shape → List ℂ)
    (sh : Fin n → Shape) (sh' : Fin m → Shape) (p : ℂ → Fin n → ℂ) (q : ℂ → Fin m → ℂ) :
    List (ℂ → ℂ) :=
  (List.ofFn fun i => (List.ofFn fun j =>
    (shifts (sh i) (sh' j)).map fun b z => -(p z i + q z j + b)).flatten).flatten

private theorem pairRoots_differentiable {n m : ℕ} (shifts : Shape → Shape → List ℂ)
    (sh : Fin n → Shape) (sh' : Fin m → Shape) {p : ℂ → Fin n → ℂ} {q : ℂ → Fin m → ℂ}
    (hp : Differentiable ℂ p) (hq : Differentiable ℂ q) :
    ∀ f ∈ pairRoots shifts sh sh' p q, Differentiable ℂ f := by
  intro f hf
  unfold pairRoots at hf
  obtain ⟨_, hi, hm⟩ := List.mem_flatten.mp hf
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hi
  obtain ⟨_, hj, hm⟩ := List.mem_flatten.mp hm
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hm
  exact (((differentiable_pi.mp hp i).add (differentiable_pi.mp hq j)).add_const b).neg

private theorem shiftProduct_eq_movingRootProduct {n m : ℕ} (shifts : Shape → Shape → List ℂ)
    (sh : Fin n → Shape) (sh' : Fin m → Shape) (p : ℂ → Fin n → ℂ) (q : ℂ → Fin m → ℂ)
    (z s : ℂ) :
    (∏ i, ∏ j, shiftProduct (shifts (sh i) (sh' j)) (s + (p z i + q z j))) =
      movingRootProduct (pairRoots shifts sh sh' p q) (z, s) /
        (2 * (Real.pi : ℂ)) ^ (pairRoots shifts sh sh' p q).length := by
  rw [movingRootProduct, ← List.length_map (f := fun r : ℂ → ℂ => s - r z), ← prod_map_div_const]
  simp only [pairRoots, List.map_map, List.map_flatten, List.prod_flatten, List.map_ofFn,
    List.prod_ofFn, Function.comp_def, shiftProduct, sub_neg_eq_add, add_assoc]

private theorem differentiable_movingRootSlice (roots : List (ℂ → ℂ)) (z : ℂ) :
    Differentiable ℂ (fun s : ℂ => movingRootProduct roots (z, s)) := by
  induction roots with
  | nil => exact differentiable_const _
  | cons r rs ih => exact (differentiable_id.sub_const (r z)).mul ih

private theorem differentiable_spectralSlice {R : ℝ} {F : ℂ × ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 R ×ˢ (univ : Set ℂ))) {z : ℂ} (hz : z ∈ ball 0 R) :
    Differentiable ℂ (fun s : ℂ => F (z, s)) := by
  apply differentiableOn_univ.mp
  exact hF.comp (Differentiable.prodMk (differentiable_const z) differentiable_id).differentiableOn
    (fun s _ => ⟨hz, mem_univ s⟩)

private theorem frequently_imaginary_in_disk {R : ℝ} (hR : 0 < R) :
    ∃ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ball 0 R ∧ z.re = 0 := by
  let j (x : ℝ) := Complex.I * (x : ℂ)
  have hj₀ : j 0 = 0 := by simp [j]
  have hj : Continuous j := by fun_prop
  have ht : Tendsto j (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · rw [← hj₀]
      exact (hj.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    · have hne : ∀ᶠ x in 𝓝[≠] (0 : ℝ), x ≠ 0 := self_mem_nhdsWithin
      filter_upwards [hne] with x hx
      exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hx)
  have hball : ∀ᶠ x in 𝓝[≠] (0 : ℝ), j x ∈ ball 0 R :=
    ht.eventually (nhdsWithin_le_nhds (ball_mem_nhds _ hR))
  apply ht.frequently
  exact (hball.mono fun x hx => ⟨hx, by simp [j, Complex.mul_re]⟩).frequently

/-- For a holomorphic one-parameter family of inducing exponents, start with a jointly
holomorphic normalization by the expanded position factors. If the meromorphic
functional equation with the block factors and holomorphy on `Re s > 0` hold at
purely imaginary values of the family parameter, the primal ordinary integral
has an entire normalization by the prescribed block factor at every parameter. -/
def RealBlockFamilyNormalizationStatement : Prop :=
  ∀ (R : ℝ), 0 < R →
    ∀ {n m : ℕ} (sh : Fin n → Shape) (sh' : Fin m → Shape) (p : ℂ → Fin n → ℂ)
      (q : ℂ → Fin m → ℂ) (b : ℝˣ) (c : ℝ≥0) (hc : 0 < c) (sign : ℂ),
    Differentiable ℂ p → Differentiable ℂ q → sign ≠ 0 →
    ∀ (F Z Zd : ℂ × ℂ → ℂ),
      DifferentiableOn ℂ F (ball 0 R ×ˢ (univ : Set ℂ)) →
      (∀ z ∈ ball 0 R, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        F (z, s) = (realPairLFactor (expand (blockList sh (p z)))
          (expand (blockList sh' (q z)))).denominator s * Z (z, s)) →
      (∀ z ∈ ball 0 R, z.re = 0 →
        DifferentiableOn ℂ (fun s => Z (z, s)) {s : ℂ | 0 < s.re} ∧
        DifferentiableOn ℂ (fun s => Zd (z, s)) {s : ℂ | 0 < s.re} ∧
        ContinuationPackage (fun s => Z (z, s)) (fun s => Zd (z, s))
          (fun s => ((realPairLFactor (blockList sh (p z)) (blockList sh' (q z))).denominator s)⁻¹)
          (fun s => ((realPairLFactor ((blockList sh (p z)).map RealLocalJacquet.dualBlock)
            ((blockList sh' (q z)).map RealLocalJacquet.dualBlock)).denominator s)⁻¹)
          (fun s => (realPairEpsilon (blockList sh (p z)) (blockList sh' (q z)) b c hc s : ℂ)) sign) →
      ∀ z ∈ ball 0 R, Nonempty (OrdinaryIntegralNormalization (fun s => Z (z, s))
        (fun s => ((realPairLFactor (blockList sh (p z)) (blockList sh' (q z))).denominator s)⁻¹))

theorem realBlockFamilyNormalization : RealBlockFamilyNormalizationStatement := by
  intro R hR n m sh sh' p q b c hc sign hp hq hsign F Z Zd hF htrace hInit
  obtain ⟨shifts, hpoly⟩ := realPositionPairPolynomial
  let roots := pairRoots shifts sh sh' p q
  let scale : ℂ := (2 * (Real.pi : ℂ)) ^ roots.length
  have hscale : scale ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  let D (z : ℂ) := realPairLFactor (blockList sh (p z)) (blockList sh' (q z))
  let Dd (z : ℂ) := realPairLFactor ((blockList sh (p z)).map RealLocalJacquet.dualBlock)
    ((blockList sh' (q z)).map RealLocalJacquet.dualBlock)
  let L (z : ℂ) := realPairLFactor (expand (blockList sh (p z))) (expand (blockList sh' (q z)))
  have hL (z s : ℂ) :
      (L z).denominator s = (movingRootProduct roots (z, s) / scale) * (D z).denominator s :=
    (hpoly sh sh' (p z) (q z) s).trans (congrArg (· * (D z).denominator s)
      (shiftProduct_eq_movingRootProduct shifts sh sh' p q z s))
  have hseed : ∃ᶠ z in 𝓝[≠] (0 : ℂ), ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      ∀ s, F (z, s) = movingRootProduct roots (z, s) * G s := by
    refine (frequently_imaginary_in_disk hR).mono ?_
    rintro z ⟨hz, hre⟩
    obtain ⟨hZ, hZd, heq⟩ := hInit z hz hre
    let E (s : ℂ) := (realPairEpsilon (blockList sh (p z)) (blockList sh' (q z)) b c hc s : ℂ)
    have hE : Differentiable ℂ E := ArchimedeanRealPairFactor.realEpsilon_differentiable _ b c hc
    obtain ⟨N, _, hN, _, hNZ, _, _⟩ := realOverlappingNormalization _ _ (D z) (Dd z) E sign 0 0
      (by norm_num) hsign hE (fun _ => Units.ne_zero _) hZ hZd heq
    let G (s : ℂ) := N s / scale
    have hG : Differentiable ℂ G := hN.div_const _
    refine ⟨G, hG, ?_⟩
    obtain ⟨σ, hσ⟩ := htrace z hz
    let τ := max σ 0
    have hτ : τ < ((τ + 1 : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; exact lt_add_one _
    have heq' : (fun s => F (z, s)) = (fun s => movingRootProduct roots (z, s) * G s) := by
      apply AnalyticOnNhd.eq_of_eventuallyEq (fun s _ => (differentiable_spectralSlice hF hz).analyticAt s)
        (fun s _ => ((differentiable_movingRootSlice roots z).mul hG).analyticAt s)
        (z₀ := ((τ + 1 : ℝ) : ℂ))
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hτ] with s hs
      change F (z, s) = movingRootProduct roots (z, s) * (N s / scale)
      rw [hσ s ((le_max_left _ _).trans_lt hs), hL z s, hNZ s ((le_max_right _ _).trans_lt hs)]
      ring
    exact congrFun heq'
  obtain ⟨G, hG, hmul⟩ := movingRootDivision R hR F roots hF
    (fun f hf => (pairRoots_differentiable shifts sh sh' hp hq f hf).differentiableOn) hseed
  intro z hz
  obtain ⟨σ, hσ⟩ := htrace z hz
  obtain ⟨τ, hτ⟩ := ArchimedeanRealPairFactor.realLFactor_ne_zero
    (realPairBlocks (expand (blockList sh (p z))) (expand (blockList sh' (q z))))
  obtain ⟨τ', hτ'⟩ := ArchimedeanRealPairFactor.realLFactor_ne_zero
    (realPairBlocks (blockList sh (p z)) (blockList sh' (q z)))
  have hslice := differentiable_spectralSlice hG hz
  refine ⟨⟨fun s => scale * G (z, s), fun s _ => (hslice.const_mul scale).analyticAt s,
    ⟨max σ (max τ τ'), fun s hs => ?_⟩⟩⟩
  have hsσ : σ < s.re := (le_max_left _ _).trans_lt hs
  have hsτ : τ < s.re := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hs)
  have hsτ' : τ' < s.re := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hs)
  have hne : movingRootProduct roots (z, s) ≠ 0 := by
    intro hx
    have h := hτ s hsτ
    change (L z).denominator s ≠ 0 at h
    rw [hL z s, hx, zero_div, zero_mul] at h
    exact h rfl
  have he := hmul (z, s) ⟨hz, mem_univ _⟩
  rw [hσ s hsσ, hL z s] at he
  have hval : (D z).denominator s * Z (z, s) = scale * G (z, s) := by
    apply mul_left_cancel₀ (div_ne_zero hne hscale)
    rw [← mul_assoc, he, ← mul_assoc, div_mul_cancel₀ _ hscale]
  have hD : (D z).denominator s ≠ 0 := hτ' s hsτ'
  change Z (z, s) = (scale * G (z, s)) * ((D z).denominator s)⁻¹
  rw [← hval, mul_comm ((D z).denominator s), mul_assoc, mul_inv_cancel₀ hD, mul_one]

end Langlands.Global.RankinSelbergGlobal.RealBlockParameters
