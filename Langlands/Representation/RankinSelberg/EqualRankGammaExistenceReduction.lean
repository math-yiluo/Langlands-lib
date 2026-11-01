import Langlands.Representation.RankinSelberg.RationalGammaComparison
import Langlands.Representation.RankinSelberg.EqualRankTrilinearUniquenessStatement
import Langlands.Representation.RankinSelberg.ModelMinusOneScalar
import Langlands.Representation.RankinSelberg.DualModels

/-!
# Algebraic comparison for equal-rank gamma existence

Cross identities for normalized trilinear forms produce one rational gamma
comparison function. The final p-adic assembly supplies the explicit inputs.
-/

noncomputable section

namespace Langlands.RankinSelberg.EqualRankGammaReduction

open LocalFactor

universe u₁ u₂ u₃

/-- At-most-one-dimensionality gives a cross identity even when the first
form vanishes. No nonzero anchor is needed at this point. -/
theorem trilinear_cross_of_unique
    {M : Type u₁} [AddCommGroup M] [Module ℂ M]
    {M' : Type u₂} [AddCommGroup M'] [Module ℂ M']
    {S : Type u₃} [AddCommGroup S] [Module ℂ S]
    (B Bd : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] ℂ)
    (h : B ≠ 0 → ∃ c : ℂ, Bd = c • B)
    (f g : M) (f' g' : M') (Φ Ψ : S) :
    Bd f f' Φ * B g g' Ψ = Bd g g' Ψ * B f f' Φ := by
  by_cases hB : B = 0
  · simp [hB]
  · obtain ⟨c, rfl⟩ := h hB
    simp only [LinearMap.smul_apply, smul_eq_mul]
    ring

/-- Cancel the two normalizing polynomials away from their finitely many roots
and apply the published spectral-to-rational comparison theorem. -/
theorem rational_cross_of_normalized_cross
    {ι : Type*} {q : ℕ} (hq : 1 < q)
    {δ : ℂˣ} (hδ : (δ : ℂ) = (q : ℂ)⁻¹)
    (R Rd : ι → RationalFunctions)
    (P Pd : Polynomial ℂ) (hP : P ≠ 0) (hPd : Pd ≠ 0)
    (B Bd : ℂ → ι → ℂ) (E : Finset ℂ)
    (hB : ∀ s i, (R i).denom.eval (spectralPoint q s) ≠ 0 →
      B s i = P.eval (spectralPoint q s) *
        RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) (R i))
    (hBd : ∀ s i, (Rd i).denom.eval (spectralPoint q (1 - s)) ≠ 0 →
      Bd s i = Pd.eval (spectralPoint q (1 - s)) *
        RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - s)) (Rd i))
    (hcross : ∀ s, spectralPoint q s ∉ E → ∀ i j,
      Bd s i * B s j = Bd s j * B s i) :
    ∀ i j, RationalReflection.subst δ (Rd i) * R j =
      RationalReflection.subst δ (Rd j) * R i := by
  classical
  let E' := (E ∪ P.roots.toFinset) ∪
    Pd.roots.toFinset.image (fun z => (δ : ℂ) / z)
  intro i j
  apply RationalGammaComparison.rational_cross_of_spectral_cross hq hδ
    (R j) (Rd j) (R i) (Rd i) E'
  intro s hs hRj hRdj hRi hRdi
  have hE : spectralPoint q s ∉ E := by
    intro hz
    exact hs (Finset.mem_union_left _ (Finset.mem_union_left _ hz))
  have hPe : P.eval (spectralPoint q s) ≠ 0 := by
    intro hz
    have hr : spectralPoint q s ∈ P.roots.toFinset :=
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).mpr hz)
    exact hs (Finset.mem_union_left _ (Finset.mem_union_right _ hr))
  have hPde : Pd.eval (spectralPoint q (1 - s)) ≠ 0 := by
    intro hz
    have hr : spectralPoint q (1 - s) ∈ Pd.roots.toFinset :=
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hPd).mpr hz)
    have href : (δ : ℂ) / spectralPoint q (1 - s) = spectralPoint q s := by
      rw [hδ]
      simpa only [sub_sub_cancel] using (spectralPoint_one_sub hq (1 - s)).symm
    exact hs (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hr, href⟩))
  have hc := hcross s hE i j
  rw [hBd s i hRdi, hBd s j hRdj, hB s i hRi, hB s j hRj] at hc
  apply mul_left_cancel₀ (mul_ne_zero hPde hPe)
  calc
    _ = (Pd.eval (spectralPoint q (1 - s)) *
          RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - s)) (Rd i)) *
        (P.eval (spectralPoint q s) *
          RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) (R j)) := by ring
    _ = _ := hc
    _ = _ := by ring

/-- A nonzero original rational value suffices for the gamma predicate, which
does not itself require the comparison rational function to be nonzero. -/
theorem exists_gamma_of_normalized_cross
    {ι : Type*} {q : ℕ} (hq : 1 < q)
    (δ ζ : ℂˣ) (hδ : (δ : ℂ) = (q : ℂ)⁻¹) (e : ℕ)
    (R Rd : ι → RationalFunctions) (hR : ∃ i, R i ≠ 0)
    (P Pd : Polynomial ℂ) (hP : P ≠ 0) (hPd : Pd ≠ 0)
    (B Bd : ℂ → ι → ℂ) (E : Finset ℂ)
    (hB : ∀ s i, (R i).denom.eval (spectralPoint q s) ≠ 0 →
      B s i = P.eval (spectralPoint q s) *
        RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) (R i))
    (hBd : ∀ s i, (Rd i).denom.eval (spectralPoint q (1 - s)) ≠ 0 →
      Bd s i = Pd.eval (spectralPoint q (1 - s)) *
        RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - s)) (Rd i))
    (hcross : ∀ s, spectralPoint q s ∉ E → ∀ i j,
      Bd s i * B s j = Bd s j * B s i) :
    ∃ G : RationalFunctions, ∀ i, GammaFunctionalEquation q ζ e G (R i) (Rd i) := by
  obtain ⟨i₀, hi₀⟩ := hR
  refine ⟨RationalGammaComparison.gammaRatio δ ζ e (R i₀) (Rd i₀), fun i => ?_⟩
  apply RationalGammaComparison.gammaFunctionalEquation_of_rational_identity hq hδ
  apply RationalGammaComparison.gammaRatio_identity δ ζ e hi₀
  exact rational_cross_of_normalized_cross hq hδ R Rd P Pd hP hPd B Bd E
    hB hBd hcross i i₀

section ActualModels

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}

/-- Assemble the actual gamma predicate once analytic continuation, Fourier
closure, and normalized continued forms with proportionality are supplied.
The companion gamma-existence proof supplies these hypotheses. -/
theorem gammaEquation_of_continuedForms
    (hq : 1 < q)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    (hAd : EqualRankAnalyticConclusion q (ψ.scale (-1)) abv μ
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ'))
    (hFourier : RowFourierClosed ψ ν (n + 1))
    (P Pd : Polynomial ℂ)
    (hP : IsNormalizedGenerator (equalRankRationalValues q ψ abv μ π σ ℓ ℓ') P)
    (hPd : Pd ≠ 0)
    (B Bd : ℂ → (coefficientModel π ℓ).toSubmodule →ₗ[ℂ]
      (coefficientModel σ ℓ').toSubmodule →ₗ[ℂ]
      SchwartzBruhat (Fin (n + 1) → F) →ₗ[ℂ] ℂ)
    (hEval : ∀ f f' Φ Φhat R Rd,
      IsRowFourierPair ψ ν Φ Φhat →
      HasRationalContinuation q (equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ) R →
      HasRationalContinuation q (dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φhat) Rd →
      ∀ s : ℂ,
        (R.denom.eval (spectralPoint q s) ≠ 0 →
          B s f f' Φ = P.eval (spectralPoint q s) *
            RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) R) ∧
        (Rd.denom.eval (spectralPoint q (1 - s)) ≠ 0 →
          Bd s f f' Φ = Pd.eval (spectralPoint q (1 - s)) *
            RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - s)) Rd))
    (E : Finset ℂ)
    (hUnique : ∀ s, spectralPoint q s ∉ E →
      B s ≠ 0 → ∃ c : ℂ, Bd s = c • B s) :
    ∃ G : RationalFunctions, EqualRankGammaEquation q ψ abv μ ν π σ ℓ ℓ' G := by
  classical
  choose Fourier hFourierPair using hFourier
  choose R hR using hA.2.1
  have hDual : ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∀ f' : (coefficientModel σ ℓ').toSubmodule,
      ∀ Φ : SchwartzBruhat (Fin (n + 1) → F),
      ∃ Rd : RationalFunctions, HasRationalContinuation q
        (dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ) Rd :=
    fun f f' Φ => hAd.2.1 (firstDualModelMap ψ π ℓ f)
      (secondDualModelMap ψ σ ℓ' f') Φ
  choose Rd hRd using hDual
  let I := (coefficientModel π ℓ).toSubmodule ×
    (coefficientModel σ ℓ').toSubmodule × SchwartzBruhat (Fin (n + 1) → F)
  let r : I → RationalFunctions := fun i => R i.1 i.2.1 i.2.2
  let rd : I → RationalFunctions := fun i => Rd i.1 i.2.1 (Fourier i.2.2)
  have hr : ∃ i, r i ≠ 0 := by
    obtain ⟨R₀, ⟨f, f', Φ, hR₀⟩, hn⟩ := hP.exists_ne_zero
    refine ⟨⟨f, f', Φ⟩, ?_⟩
    change R f f' Φ ≠ 0
    intro hz
    exact hn ((hR₀.unique hq (hR f f' Φ)).trans hz)
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (lt_trans Nat.zero_lt_one hq).ne'
  let δ : ℂˣ := Units.mk0 (q : ℂ)⁻¹ (inv_ne_zero hq0)
  obtain ⟨ζ, hζ⟩ := exists_modelMinusOneScalar σ hσ
  have hValues := fun (s : ℂ) (i : I) =>
    hEval i.1 i.2.1 i.2.2 (Fourier i.2.2) (r i) (rd i)
      (hFourierPair i.2.2) (hR i.1 i.2.1 i.2.2)
      (hRd i.1 i.2.1 (Fourier i.2.2)) s
  obtain ⟨G, hG⟩ := exists_gamma_of_normalized_cross hq δ ζ rfl n r rd hr
    P Pd hP.polynomial_ne_zero hPd
    (fun s i => B s i.1 i.2.1 i.2.2)
    (fun s i => Bd s i.1 i.2.1 i.2.2) E
    (fun s i => (hValues s i).1) (fun s i => (hValues s i).2)
    (fun s hs i j => trilinear_cross_of_unique (B s) (Bd s) (hUnique s hs)
      i.1 j.1 i.2.1 j.2.1 i.2.2 j.2.2)
  refine ⟨G, ζ, hζ ℓ', hP.exists_ne_zero, ?_⟩
  intro f f' Φ
  exact ⟨Fourier Φ, R f f' Φ, Rd f f' (Fourier Φ), hFourierPair Φ,
    hR f f' Φ, hRd f f' (Fourier Φ), hG ⟨f, f', Φ⟩⟩

end ActualModels

end Langlands.RankinSelberg.EqualRankGammaReduction
