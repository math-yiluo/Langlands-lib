import Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingStatement
import Langlands.Global.Factors.FiniteComparisonProof

/-!
# Euler products whose value times a continued coefficient is regular and nonzero

Let `fac : ι → ℂ → ℂ` be a family of Euler factors. Suppose that at every point `s₀` of
the imaginary axis there are

* a function `coeff` and a meromorphic function `c`, analytic and nonzero at `s₀`, with
  `c s = (∏_v fac v (1 + s)) · coeff s` on a right half-plane on which the product converges
  absolutely, and
* a meromorphic function `Ec`, analytic at `s₀`, equal to `coeff` on a right half-plane.

Then the Euler product `∏_v fac v s` has a meromorphic continuation `L` to `ℂ`, and `L` has
nonpositive order (no zero) at every point `1 + iy`. This is the formal step of the proof of
Shahidi 1981, Theorems 5.1 and 5.2 (pp. 351–353), in which the generic Fourier coefficient
`coeff` of a cuspidal Eisenstein series equals a nonvanishing factor `c` times
`L^S(1 + s)^(-1)`, and holomorphy of the coefficient on the imaginary axis then excludes zeros
of `L^S` on the line `Re s = 1`.

The continuation is `L (1 + s) = c s / Ec s`, corrected at the zeros of `Ec` in the
half-plane of convergence, where it is the value of the product. `Ec` vanishes identically
near no point, because `c` does not. For the order at `1 + iy` the data at `s₀ = iy` are used;
any two continuations have the same order, by the identity theorem.

The last section specializes to the partial pair Euler factors of
`CuspidalPairBoundaryNonvanishingStatement`.
-/

noncomputable section

set_option autoImplicit false

open Filter Topology

universe u uQ v

namespace Langlands.Global

namespace EulerProductCoefficientData

variable {ι : Type v} (fac : ι → ℂ → ℂ)

/-- Coefficient data at a point `s₀`: a function `coeff`, a meromorphic `c`, analytic and
nonzero at `s₀`, with `c s = (∏_v fac v (1 + s)) * coeff s` on a right half-plane where the
product converges absolutely, and a meromorphic `Ec` analytic at `s₀` that agrees with
`coeff` on a right half-plane. -/
def CoefficientData (s₀ : ℂ) : Prop :=
  ∃ coeff c Ec : ℂ → ℂ, Meromorphic c ∧ AnalyticAt ℂ c s₀ ∧ c s₀ ≠ 0 ∧
    Meromorphic Ec ∧ AnalyticAt ℂ Ec s₀ ∧
    (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Summable (fun v => ‖fac v (1 + s) - 1‖) ∧
        ∃ Λ : ℂ, HasProd (fun v => fac v (1 + s)) Λ ∧ c s = Λ * coeff s) ∧
    ∃ σ' : ℝ, ∀ s : ℂ, σ' < s.re → Ec s = coeff s

/-- `L` represents the Euler product of `fac`: meromorphic, and on a right half-plane the
product converges absolutely to `L s`. -/
def IsRepresentative (L : ℂ → ℂ) : Prop :=
  Meromorphic L ∧ ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
    Summable (fun v => ‖fac v s - 1‖) ∧ HasProd (fun v => fac v s) (L s)

variable {fac}

/-- Two representatives have the same order everywhere. -/
theorem IsRepresentative.meromorphicOrderAt_eq {L L' : ℂ → ℂ} (hL : IsRepresentative fac L)
    (hL' : IsRepresentative fac L') (z : ℂ) :
    meromorphicOrderAt L z = meromorphicOrderAt L' z := by
  obtain ⟨σ, hσ⟩ := hL.2
  obtain ⟨σ', hσ'⟩ := hL'.2
  refine meromorphicOrderAt_congr (FunctionalEquationComparison.eq_on_halfplane_meromorphicEq
    (σ := max σ σ') hL.1 hL'.1 (fun s hs => ?_) z)
  exact (hσ s (lt_of_le_of_lt (le_max_left _ _) hs)).2.unique
    (hσ' s (lt_of_le_of_lt (le_max_right _ _) hs)).2

/-- From coefficient data, the continued coefficient `Ec` vanishes identically near no point. -/
theorem eventually_ne_zero_of_data {coeff c Ec : ℂ → ℂ} {s₀ : ℂ} (hc : Meromorphic c)
    (hcs₀ : AnalyticAt ℂ c s₀) (hc0 : c s₀ ≠ 0) (hEc : Meromorphic Ec) {σ σ' : ℝ}
    (hσ : ∀ s : ℂ, σ < s.re → ∃ Λ : ℂ, c s = Λ * coeff s)
    (hσ' : ∀ s : ℂ, σ' < s.re → Ec s = coeff s) (z : ℂ) :
    ∀ᶠ s in 𝓝[≠] z, Ec s ≠ 0 := by
  rw [← meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hEc z)]
  intro htop
  set z₁ : ℂ := ((max σ σ' + 1 : ℝ) : ℂ)
  have hz₁ : max σ σ' < z₁.re := by simp [z₁]
  have hE₁ : meromorphicOrderAt Ec z₁ = ⊤ :=
    hEc.meromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ z) (Set.mem_univ z₁) htop
  have hnhds : ∀ᶠ s : ℂ in 𝓝 z₁, max σ σ' < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₁
  have hc₁ : meromorphicOrderAt c z₁ = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp hE₁,
      hnhds.filter_mono nhdsWithin_le_nhds] with s hs hre
    obtain ⟨Λ, hΛ⟩ := hσ s (lt_of_le_of_lt (le_max_left _ _) hre)
    rw [hΛ, ← hσ' s (lt_of_le_of_lt (le_max_right _ _) hre), hs, mul_zero]
  have hc₀ : meromorphicOrderAt c s₀ = ⊤ :=
    hc.meromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ z₁) (Set.mem_univ s₀) hc₁
  rw [hcs₀.meromorphicOrderAt_eq, (hcs₀.analyticOrderAt_eq_zero).mpr hc0] at hc₀
  simp at hc₀

/-- The representative built from coefficient data, in the shifted variable `s = w - 1`:
the Euler product value on the half-plane `M < re s`, and `c s / Ec s` elsewhere. -/
def shiftedRepresentative (fac : ι → ℂ → ℂ) (c Ec : ℂ → ℂ) (M : ℝ) (s : ℂ) : ℂ :=
  if M < s.re then ∏' v, fac v (1 + s) else c s / Ec s

/-- Coefficient data at `s₀` give a representative `L` with `L (1 + s) = c s / Ec s` in a
punctured neighbourhood of every point. -/
theorem exists_representative_of_data {s₀ : ℂ} (h : CoefficientData fac s₀) :
    ∃ (c Ec : ℂ → ℂ) (L : ℂ → ℂ), AnalyticAt ℂ c s₀ ∧ c s₀ ≠ 0 ∧ AnalyticAt ℂ Ec s₀ ∧
      IsRepresentative fac L ∧ (∀ z : ℂ, ∀ᶠ s in 𝓝[≠] z, Ec s ≠ 0) ∧
      ∀ z : ℂ, (fun s => L (1 + s)) =ᶠ[𝓝[≠] z] fun s => c s / Ec s := by
  obtain ⟨coeff, c, Ec, hc, hcs₀, hc0, hEc, hEcs₀, ⟨σ, hσ⟩, σ', hσ'⟩ := h
  have hne := eventually_ne_zero_of_data hc hcs₀ hc0 hEc
    (fun s hs => ((hσ s hs).2).imp fun Λ hΛ => hΛ.2) hσ'
  set M : ℝ := max σ σ'
  set G : ℂ → ℂ := shiftedRepresentative fac c Ec M
  -- `G` agrees with `c / Ec` off the zeros of `Ec`.
  have hG : ∀ s : ℂ, Ec s ≠ 0 → G s = c s / Ec s := by
    intro s hs
    by_cases hre : M < s.re
    · obtain ⟨-, Λ, hprod, hcΛ⟩ := hσ s (lt_of_le_of_lt (le_max_left _ _) hre)
      have hE : Ec s = coeff s := hσ' s (lt_of_le_of_lt (le_max_right _ _) hre)
      simp only [G, shiftedRepresentative, hre, ↓reduceIte, hprod.tprod_eq]
      rw [hcΛ, ← hE, mul_div_assoc, div_self hs, mul_one]
    · simp only [G, shiftedRepresentative, hre, ↓reduceIte]
  have hGev : ∀ z : ℂ, G =ᶠ[𝓝[≠] z] fun s => c s / Ec s := fun z => by
    filter_upwards [hne z] with s hs using hG s hs
  have hGmero : Meromorphic G := fun z =>
    ((hc z).div (hEc z)).congr (hGev z).symm
  refine ⟨c, Ec, fun w => G (w - 1), hcs₀, hc0, hEcs₀, ⟨?_, 1 + M, fun s hs => ?_⟩, hne,
    fun z => ?_⟩
  · exact Meromorphic.meromorphic_fun_comp_sub_const_iff_meromorphic.mpr hGmero
  · have hre : M < (s - 1).re := by simp; linarith
    obtain ⟨hsum, Λ, hprod, -⟩ := hσ (s - 1) (lt_of_le_of_lt (le_max_left _ _) hre)
    have e : 1 + (s - 1) = s := by ring
    rw [e] at hsum hprod
    refine ⟨hsum, ?_⟩
    simp only [G, shiftedRepresentative, hre, ↓reduceIte, e, hprod.tprod_eq]
    exact hprod
  · filter_upwards [hGev z] with s hs
    simp only [add_sub_cancel_left]
    exact hs

/-- **Derivation core.** If coefficient data exist at every point of the imaginary axis, then
the Euler product of `fac` has a representative with nonpositive order at every `1 + iy`. -/
theorem exists_representative_order_nonpos
    (H : ∀ s₀ : ℂ, s₀.re = 0 → CoefficientData fac s₀) :
    ∃ L : ℂ → ℂ, IsRepresentative fac L ∧
      ∀ y : ℝ, meromorphicOrderAt L (1 + y * Complex.I) ≤ 0 := by
  obtain ⟨-, -, L₀, -, -, -, hL₀, -, -⟩ := exists_representative_of_data (H 0 (by simp))
  refine ⟨L₀, hL₀, fun y => ?_⟩
  obtain ⟨c, Ec, L, hcy, hc0, hEcy, hL, hne, hev⟩ :=
    exists_representative_of_data (H (y * Complex.I) (by simp))
  rw [hL₀.meromorphicOrderAt_eq hL]
  -- order of `L` at `1 + iy` = order of `s ↦ L (1 + s)` at `iy`
  have hshift : meromorphicOrderAt L (1 + y * Complex.I) =
      meromorphicOrderAt (fun s => L (1 + s)) (y * Complex.I) := by
    have := meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt (f := L) (c := 1)
      (x := (y * Complex.I : ℂ))
    simp only [add_comm _ (1 : ℂ)] at this
    exact this.symm
  rw [hshift, meromorphicOrderAt_congr (hev _)]
  have hdiv : (fun s => c s / Ec s) = c * Ec⁻¹ := by
    funext s; simp [div_eq_mul_inv]
  rw [hdiv, meromorphicOrderAt_mul hcy.meromorphicAt hEcy.meromorphicAt.inv,
    meromorphicOrderAt_inv, hcy.meromorphicOrderAt_eq, (hcy.analyticOrderAt_eq_zero).mpr hc0]
  have hfin : meromorphicOrderAt Ec (y * Complex.I) ≠ ⊤ :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hEcy.meromorphicAt).mpr (hne _)
  have hnn : 0 ≤ meromorphicOrderAt Ec (y * Complex.I) := hEcy.meromorphicOrderAt_nonneg
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfin
  rw [← hn] at hnn ⊢
  have : (0 : ℤ) ≤ n := by exact_mod_cast hnn
  simp only [ENat.map_zero, CharP.cast_eq_zero, WithTop.coe_zero, zero_add]
  exact_mod_cast (neg_nonpos.mpr this)

end EulerProductCoefficientData

open EulerProductCoefficientData

/-- **Coefficient data on the imaginary axis exclude zeros on `Re s = 1`.** For every family
of Euler factors `fac : ι → ℂ → ℂ` with coefficient data at every point of the imaginary
axis, the Euler product of `fac` has a meromorphic continuation to `ℂ` with nonpositive order
at every point `1 + iy`, `y` real. -/
def EulerProductCoefficientDataReductionStatement : Prop :=
  ∀ (ι : Type v) (fac : ι → ℂ → ℂ),
    (∀ s₀ : ℂ, s₀.re = 0 → CoefficientData fac s₀) →
      ∃ L : ℂ → ℂ, IsRepresentative fac L ∧
        ∀ y : ℝ, meromorphicOrderAt L (1 + y * Complex.I) ≤ 0

/-- **`EulerProductCoefficientDataReductionStatement`.** -/
theorem eulerProductCoefficientDataReduction :
    EulerProductCoefficientDataReductionStatement.{v} :=
  fun _ _ H => exists_representative_order_nonpos H

namespace EulerProductCoefficientData

/-! ### Partial pair Euler factors -/

open NumberField CuspidalPairBoundaryNonvanishing
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {P : CuspidalSpectralPresentation.{u, uQ} T} {P' : CuspidalSpectralPresentation.{u, uQ} T'}

/-- `IsPartialPairLFunction` is `IsRepresentative` for the partial Euler factors. -/
theorem isPartialPairLFunction_iff {S : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S)
    (hP' : P'.exceptional ⊆ S) (L : ℂ → ℂ) :
    IsPartialPairLFunction P P' hP hP' L ↔
      IsRepresentative (partialEulerFactor P P' hP hP') L := by
  unfold IsPartialPairLFunction IsRepresentative
  rw [meromorphicOn_univ]

/-- **The premise for one `S`.** If coefficient data for the partial Euler factors outside
some `S₀ ⊇ S` exist at every point of the imaginary axis, then the conclusion of
`CuspidalPairBoundaryNonvanishingEnlargedStatement` holds for `S`. -/
theorem enlarged_of_coefficientData {S S₀ : Finset (FinitePlace F)} (hP : P.exceptional ⊆ S)
    (hP' : P'.exceptional ⊆ S) (hS : S ⊆ S₀)
    (H : ∀ s₀ : ℂ, s₀.re = 0 →
      CoefficientData (partialEulerFactor P P' (hP.trans hS) (hP'.trans hS)) s₀) :
    ∃ (S₀ : Finset (FinitePlace F)) (hS : S ⊆ S₀) (L₀ : ℂ → ℂ),
      IsPartialPairLFunction P P' (hP.trans hS) (hP'.trans hS) L₀ ∧
        ∀ y : ℝ, meromorphicOrderAt L₀ (1 + y * Complex.I) ≤ 0 := by
  obtain ⟨L₀, hL₀, hord⟩ := exists_representative_order_nonpos H
  exact ⟨S₀, hS, L₀, (isPartialPairLFunction_iff _ _ L₀).mpr hL₀, hord⟩

end EulerProductCoefficientData

end Langlands.Global
