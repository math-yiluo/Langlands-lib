import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsStatement
import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroGammaStatement
import Langlands.Representation.RankinSelberg.RationalGammaComparison

/-!
# Conditional comparison of continued unequal-rank bilinear forms

The fixed-data uniqueness predicate is the exact specialization of the
published full uniqueness statement. Given that predicate, continued forms,
actual continuations and separate nonzero witnesses, the comparison is algebraic.
No analytic, covariance or uniqueness existence theorem is proved here.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration LocalFactor

universe uF uV uW

/-- Two bilinear forms have vanishing cross difference if the second is a
scalar multiple whenever the first is nonzero. No scalar is needed when the
first form is zero. -/
theorem bilinear_cross_of_scalar_comparison
    {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B]
    (L L' : A →ₗ[ℂ] B →ₗ[ℂ] ℂ)
    (h : L ≠ 0 → ∃ c : ℂ, L' = c • L)
    (a c : A) (b d : B) :
    L' a b * L c d = L' c d * L a b := by
  by_cases hL : L = 0
  · simp [hL]
  · obtain ⟨z, rfl⟩ := h hL
    simp only [LinearMap.smul_apply, smul_eq_mul]
    ring

section FixedData

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Fixed-data specialization of the conclusion of
`UnequalRankBilinearUniquenessStatement`. This predicate does not prove
uniqueness; it records that conclusion as an explicit conditional input. -/
def UnequalRankBilinearUniquenessConclusion (hnr : n < r)
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) : Prop :=
  let M := (coefficientModel π ℓ).toSubmodule
  let M' := (coefficientModel σ ℓ').toSubmodule
  ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint q s ∉ E →
    ∀ B B' : M →ₗ[ℂ] M' →ₗ[ℂ] ℂ,
      IsUnequalRankBilinearCovariant hnr ψ abv π σ ℓ ℓ' s B →
      IsUnequalRankBilinearCovariant hnr ψ abv π σ ℓ ℓ' s B' →
      B ≠ 0 → ∃ c : ℂ, B' = c • B

variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ} {hnr : n < r}

/-- Continued covariant forms and fixed-data uniqueness imply all reflected
rational cross identities for the supplied actual continuations. -/
theorem UnequalRankBlockZeroContinuedFormsConclusion.rational_cross
    (hforms : UnequalRankBlockZeroContinuedFormsConclusion hnr q ψ abv μ ν π σ ℓ ℓ')
    (hunique : UnequalRankBilinearUniquenessConclusion hnr q ψ abv π σ ℓ ℓ')
    (hq : 1 < q) {δ : ℂˣ} (hδ : (δ : ℂ) = (q : ℂ)⁻¹)
    (R Rd : (coefficientModel π ℓ).toSubmodule →
      (coefficientModel σ ℓ').toSubmodule → RationalFunctions)
    (hR : ∀ f f', HasRationalContinuation q
      (unequalRankIntegralAt 0 (r - n - 1) (by omega) ψ abv μ
        (rectangularMeasure ν 0 (n + 1)) f.val f'.val) (R f f'))
    (hRd : ∀ f f', HasRationalContinuation q
      (dualUnequalRankModelIntegralAt hnr 0 (r - n - 1) (by omega)
        ψ abv μ ν π σ ℓ ℓ' f f') (Rd f f')) :
    ∀ f f' g g', RationalReflection.subst δ (Rd f f') * R g g' =
      RationalReflection.subst δ (Rd g g') * R f f' := by
  classical
  obtain ⟨EC, hC⟩ := hforms
  obtain ⟨EU, hU⟩ := hunique
  intro f f' g g'
  apply RationalGammaComparison.rational_cross_of_spectral_cross hq hδ
    (R g g') (Rd g g') (R f f') (Rd f f') (EC ∪ EU)
  intro s hs _ _ _ _
  have hsC : spectralPoint q s ∉ EC := fun hx =>
    hs (Finset.mem_union.mpr (Or.inl hx))
  have hsU : spectralPoint q s ∉ EU := fun hx =>
    hs (Finset.mem_union.mpr (Or.inr hx))
  obtain ⟨B, Bd, hB, hBd, hBR, hBdR⟩ := hC s hsC
  rw [← (hBdR f f' _ (hRd f f')).2, ← (hBR g g' _ (hR g g')).2,
    ← (hBdR g g' _ (hRd g g')).2, ← (hBR f f' _ (hR f f')).2]
  exact bilinear_cross_of_scalar_comparison B Bd (hU s hsU B Bd hB hBd) f g f' g'

/-- Conditional block-zero gamma assembly from actual continuations, separate
nonzero witnesses, continued covariant forms, fixed-data uniqueness and the
actual minus-one scalar. These inputs remain explicit obligations. -/
theorem UnequalRankBlockZeroContinuedFormsConclusion.exists_gammaEquation
    (hforms : UnequalRankBlockZeroContinuedFormsConclusion hnr q ψ abv μ ν π σ ℓ ℓ')
    (hunique : UnequalRankBilinearUniquenessConclusion hnr q ψ abv π σ ℓ ℓ')
    (hq : 1 < q) (δ ζ : ℂˣ) (hδ : (δ : ℂ) = (q : ℂ)⁻¹)
    (hζ : HasModelMinusOneScalar σ ℓ' ζ)
    (R Rd : (coefficientModel π ℓ).toSubmodule →
      (coefficientModel σ ℓ').toSubmodule → RationalFunctions)
    (hR : ∀ f f', HasRationalContinuation q
      (unequalRankIntegralAt 0 (r - n - 1) (by omega) ψ abv μ
        (rectangularMeasure ν 0 (n + 1)) f.val f'.val) (R f f'))
    (hRd : ∀ f f', HasRationalContinuation q
      (dualUnequalRankModelIntegralAt hnr 0 (r - n - 1) (by omega)
        ψ abv μ ν π σ ℓ ℓ' f f') (Rd f f'))
    (hRne : ∃ f f', R f f' ≠ 0) (hRdne : ∃ f f', Rd f f' ≠ 0) :
    ∃ G : RationalFunctions, G ≠ 0 ∧
      UnequalRankBlockZeroGammaEquation hnr q ψ abv μ ν π σ ℓ ℓ' G := by
  let I := (coefficientModel π ℓ).toSubmodule × (coefficientModel σ ℓ').toSubmodule
  have horig : ∃ i : I, R i.1 i.2 ≠ 0 := by
    obtain ⟨f, f', hf⟩ := hRne
    exact ⟨(f, f'), hf⟩
  have hdual : ∃ i : I, Rd i.1 i.2 ≠ 0 := by
    obtain ⟨f, f', hf⟩ := hRdne
    exact ⟨(f, f'), hf⟩
  have hcross := hforms.rational_cross hunique hq hδ R Rd hR hRd
  obtain ⟨G, hG, hall⟩ :=
    RationalGammaComparison.exists_gammaFunctionalEquation_of_cross hq δ ζ hδ r
      (fun i : I => R i.1 i.2) (fun i : I => Rd i.1 i.2) horig hdual
      (fun i j => hcross i.1 i.2 j.1 j.2)
  refine ⟨G, hG, ζ, hζ, ?_, ?_⟩
  · obtain ⟨f, f', hf⟩ := hRne
    refine ⟨R f f', ?_, hf⟩
    rw [unequalRankValuesAt_eq_set]
    exact ⟨f, f', hR f f'⟩
  · intro f f'
    exact ⟨R f f', Rd f f', hR f f', hRd f f', hall (f, f')⟩

end FixedData

end Langlands.RankinSelberg
