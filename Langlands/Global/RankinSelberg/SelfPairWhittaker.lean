import Langlands.Automorphic.CuspidalConjugateRealization
import Langlands.Global.RankinSelberg.EqualEulerIntegrand
import Langlands.Global.RankinSelberg.EqualAnalyticProof
import Langlands.Global.Factors.CuspidalPairPartialGammaGlobalReduction

/-! # Conjugation and positivity for self-pair Whittaker integrals -/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Global.RankinSelbergGlobal.SelfPair

open Automorphic

local instance selfPairSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance selfPairSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The cusp function of the conjugated vector is the conjugate cusp function. -/
theorem cuspFunction_conjugate {r : ℕ} (T : CuspidalOperatorRealization F r)
    (x : T.Space) (g : Points F (r + 1)) :
    cuspFunction F T.conjugate (T.conjugateEquiv x) g =
      conj (cuspFunction F T x g) := by
  simp only [UnequalAnalytic.cuspFunction_eq, T.toContinuous_conjugateEquiv,
    evaluate_continuousConj]

/-- Conjugating a vector and inverting the unitary additive character conjugates its
Whittaker coefficient. -/
theorem cuspWhittaker_conjugate {r : ℕ} (T : CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : ∀ a : Adeles F, ‖ψ a‖ = 1)
    (x : T.Space) (g : Points F (r + 1)) :
    cuspWhittaker F T.conjugate ψ⁻¹ (T.conjugateEquiv x) g =
      conj (cuspWhittaker F T ψ x g) := by
  unfold cuspWhittaker generalLinearWhittakerFunction subgroupCharacterCoefficient
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [cuspFunction_conjugate, Unfolding.genericCharacter_inv F r ψ hψ,
    map_mul]

/-- Conjugation preserves the same spherical conditions. -/
theorem isSphericalOutside_conjugate {r : ℕ} {T : CuspidalOperatorRealization F r}
    {S : Finset (FinitePlace F)} {x : T.Space} (hx : IsSphericalOutside F T S x) :
    IsSphericalOutside F T.conjugate S (T.conjugateEquiv x) := by
  intro v hv k hk
  rw [T.conjugateEquiv_finite, hx v hv k hk]

/-- A unitary character multiplied by its conjugate is trivial. -/
theorem mul_conjCharacter_eq_one (ω : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hω : ∀ a, ‖(ω a : ℂ)‖ = 1) :
    ω * conjCharacter F ω = 1 := by
  ext a
  change (ω a : ℂ) * conj (ω a : ℂ) = 1
  rw [Complex.mul_conj', hω]
  norm_num

/-- The pole set for the trivial character is exactly `{0,1}`. -/
theorem equalPoleSet_one (n : ℕ) :
    equalPoleSet F n 1 = ({0, 1} : Set ℂ) := by
  ext s
  constructor
  · rintro ⟨w, hw, hs⟩
    have hw0 : w = 0 := CuspidalPairPartialGammaGlobal.detPower_injective F (fun z => by
      have hz : (centralIdeleCharacter F 1 (ideleOf F z) : ℂ) = 1 := rfl
      simpa only [hz, detPower, zero_mul, Complex.exp_zero] using (hw z).symm)
    simpa [hw0] using hs
  · intro hs
    refine ⟨0, fun z => ?_, ?_⟩
    · change (1 : ℂ) = detPower F 1 z 0
      simp only [detPower, zero_mul, Complex.exp_zero]
    · simpa using hs

/-- The self-pair Whittaker integrand is a real nonnegative weight times a Mellin
exponential. No unfolding or integrability assumption is used here. -/
theorem equalWhittakerIntegrand_conjugate {r : ℕ}
    (T : CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ)
    (hψ : ∀ a : Adeles F, ‖ψ a‖ = 1) (x : T.Space)
    (Φ : RowVector F (r + 1) → ℝ) (s : ℂ) (q : WhittakerQuotient F (r + 1)) :
    equalWhittakerIntegrand F (cuspWhittaker F T ψ x)
        (cuspWhittaker F T.conjugate ψ⁻¹ (T.conjugateEquiv x))
        (fun y => (Φ y : ℂ)) s q =
      ((‖cuspWhittaker F T ψ x q.out‖ ^ 2 * Φ (lastRow F r q.out) : ℝ) : ℂ) *
        Complex.exp (s * (Real.log (detNorm F (r + 1) q.out) : ℂ)) := by
  simp only [equalWhittakerIntegrand, cuspWhittaker_conjugate T ψ hψ, Complex.mul_conj',
    Complex.ofReal_mul, Complex.ofReal_pow, detPower]

/-- At a real parameter, the self-pair integrand is the coercion of a nonnegative real
function when the test function is nonnegative. -/
theorem equalWhittakerIntegrand_conjugate_real {r : ℕ}
    (T : CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ)
    (hψ : ∀ a : Adeles F, ‖ψ a‖ = 1) (x : T.Space)
    (Φ : RowVector F (r + 1) → ℝ) (σ : ℝ) (q : WhittakerQuotient F (r + 1)) :
    equalWhittakerIntegrand F (cuspWhittaker F T ψ x)
        (cuspWhittaker F T.conjugate ψ⁻¹ (T.conjugateEquiv x))
        (fun y => (Φ y : ℂ)) σ q =
      ((‖cuspWhittaker F T ψ x q.out‖ ^ 2 * Φ (lastRow F r q.out) *
        Real.exp (σ * Real.log (detNorm F (r + 1) q.out)) : ℝ) : ℂ) := by
  rw [equalWhittakerIntegrand_conjugate T ψ hψ]
  simp only [Complex.ofReal_mul, Complex.ofReal_exp]

/-- The global integral of a unitary self-pair has a continuation holomorphic on
`Re s > 1`, unconditionally from the published equal-rank analytic theorem. -/
theorem exists_holomorphic_equalIntegral {r : ℕ}
    (T : CuspidalOperatorRealization F r)
    (ω : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hωu : ∀ a, ‖(ω a : ℂ)‖ = 1) (hω : T.realization.HasCentralCharacter ω)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (x : T.Space) (Φ : RowVector F (r + 1) → ℂ)
    (hΦ : Φ ∈ schwartzBruhat F (r + 1)) :
    ∃ (I : ℂ → ℂ) (σ : ℝ), DifferentiableOn ℂ I {s | 1 < s.re} ∧
      ∀ s : ℂ, σ < s.re →
        I s = equalIntegral F 1 (cuspFunction F T x)
          (cuspFunction F T.conjugate (T.conjugateEquiv x)) Φ s := by
  have hωc := OperatorRealization.HasCentralCharacter.conjugate T.realization hω
  obtain ⟨σ, I, Id, hI, hhol, -⟩ :=
    EqualAnalytic.equalAnalyticStatement_proof F r T T.conjugate ω (conjCharacter F ω)
      hω hωc ψ hψ x (T.conjugateEquiv x) Φ hΦ
  have htriv := mul_conjCharacter_eq_one ω hωu
  rw [htriv, equalPoleSet_one] at hhol
  refine ⟨I, σ, hhol.1.mono ?_, fun s hs => ?_⟩
  · intro s hs
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor <;> rintro rfl <;> norm_num at hs
  · simpa [htriv] using (hI s hs).2.2.1

/-- Once equal-rank unfolding is supplied, the same continuation agrees with the
Whittaker integral and the latter is integrable on a right half-plane. -/
theorem exists_holomorphic_equalWhittakerIntegral (hU : EqualUnfoldingStatement.{u})
    {r : ℕ} (T : CuspidalOperatorRealization F r)
    (ω : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hωu : ∀ a, ‖(ω a : ℂ)‖ = 1) (hω : T.realization.HasCentralCharacter ω)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (x : T.Space) (Φ : RowVector F (r + 1) → ℂ)
    (hΦ : Φ ∈ schwartzBruhat F (r + 1)) :
    ∃ (I : ℂ → ℂ) (σ : ℝ), DifferentiableOn ℂ I {s | 1 < s.re} ∧
      ∀ s : ℂ, σ < s.re →
        Integrable (equalWhittakerIntegrand F (cuspWhittaker F T ψ x)
          (cuspWhittaker F T.conjugate ψ⁻¹ (T.conjugateEquiv x)) Φ s)
          (whittakerQuotientMeasure F (r + 1)) ∧
        I s = equalWhittakerIntegral F (cuspWhittaker F T ψ x)
          (cuspWhittaker F T.conjugate ψ⁻¹ (T.conjugateEquiv x)) Φ s := by
  obtain ⟨I, σ, hhol, hI⟩ := exists_holomorphic_equalIntegral T ω hωu hω ψ hψ x Φ hΦ
  obtain ⟨C, -, hC⟩ :=
    hU F r T T.conjugate ω (conjCharacter F ω) hω
      (OperatorRealization.HasCentralCharacter.conjugate T.realization hω)
  refine ⟨I, max σ C, hhol, fun s hs => ?_⟩
  have hσs : σ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hCs : C < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  have h := (hC ψ hψ x (T.conjugateEquiv x) Φ hΦ).1 s hCs
  refine ⟨h.2.1, (hI s hσs).trans ?_⟩
  simpa [mul_conjCharacter_eq_one ω hωu] using h.2.2

/-- Internal consequence of the equal-rank analytic theorem: the global integral of a
unitary cuspidal realization paired with its conjugate continues holomorphically to
`Re s > 1`. This does not assert Euler factorization or equal-rank unfolding. -/
def UnitarySelfPairIntegralContinuationStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ) (T : CuspidalOperatorRealization K r)
    (ω : IdeleClassGroup (𝓞 K) K →ₜ* ℂˣ),
    (∀ a, ‖(ω a : ℂ)‖ = 1) → T.realization.HasCentralCharacter ω →
    ∀ (ψ : AddChar (Adeles K) ℂ), IsStandardAdditiveCharacter K ψ →
    ∀ (x : T.Space) (Φ : RowVector K (r + 1) → ℂ),
    Φ ∈ schwartzBruhat K (r + 1) →
    ∃ (I : ℂ → ℂ) (σ : ℝ), DifferentiableOn ℂ I {s | 1 < s.re} ∧
      ∀ s : ℂ, σ < s.re →
        I s = equalIntegral K 1 (cuspFunction K T x)
          (cuspFunction K T.conjugate (T.conjugateEquiv x)) Φ s

/-- Proof of the internal integral-continuation statement. -/
theorem unitarySelfPairIntegralContinuation :
    UnitarySelfPairIntegralContinuationStatement.{u} :=
  fun _ _ _ _ _ T ω hωu hω ψ hψ x Φ hΦ =>
    exists_holomorphic_equalIntegral T ω hωu hω ψ hψ x Φ hΦ

end Langlands.Global.RankinSelbergGlobal.SelfPair
