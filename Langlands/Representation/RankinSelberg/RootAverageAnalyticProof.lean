import Langlands.Representation.RankinSelberg.RootAverageAnalyticStatement
import Langlands.Representation.RankinSelberg.CompactRootExpansionProof
import Langlands.Representation.RankinSelberg.RationalContinuationLinearProof

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker RationalContinuationLinear
open scoped BigOperators

universe uF uV uW

/-- The Mellin premise controls the actual iterated compact root integral. -/
theorem equalRankRootAverageAnalytic {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    EqualRankRootAverageAnalyticStatement.{uF, uV, uW} F T n := by
  classical
  intro hM
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let κ := (generalLinearHaar F.Carrier n).restrict (K : Set _)
  let A := Fin (n + 1) → F.Carrierˣ
  let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F.Carrier)
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  let v : A → ℂ → ℂ := fun a s =>
    ∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((i.val + 1 : ℂ) * s)
  let I := fun (η : A → ℂ) (Ψ : SchwartzBruhat (Fin (n + 1) → F.Carrier))
    (s : ℂ) (a : A) => Ψ (fun i => (a i : F.Carrier)) * η a * v a s
  dsimp only
  intro V _ _ W _ _ π σ ψ hsπ hsσ hπ hσ
  obtain ⟨m, η, hη, hexp⟩ := equalRankCompactRootExpansion F T n V W π σ ψ hsπ hsσ hπ hσ
  let X : Finset (A → ℂ) := Finset.univ.image η
  have hX (e : A → ℂ) (he : e ∈ X) : Continuous e ∧
      FiniteDimensional ℂ (Submodule.span ℂ
        (Set.range fun b : A => fun a : A => e (b * a))) := by
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he
    exact hη j
  have hmem (j : Fin m) : η j ∈ X := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hM' := hM p inferInstance F T (n + 1) (fun i => i.val + 1)
    (fun _ => Nat.zero_lt_succ _) X hX
  simp only [Nat.cast_add, Nat.cast_one] at hM'
  change (∀ e ∈ X, ∀ Ψ, ∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (I e Ψ s) dA) ∧
    (∀ e ∈ X, ∀ Ψ, ∃ R : RationalFunctions,
      HasRationalContinuation T.residueCardinality (fun s => ∫ a, I e Ψ s a ∂dA) R) ∧
    HasCommonDenominator {R | ∃ e ∈ X, ∃ Ψ,
      HasRationalContinuation T.residueCardinality (fun s => ∫ a, I e Ψ s a ∂dA) R} at hM'
  let values : Set RationalFunctions := {R | ∃ e ∈ X, ∃ Ψ,
    HasRationalContinuation T.residueCardinality (fun s => ∫ a, I e Ψ s a ∂dA) R}
  obtain ⟨hconv, hrat, D, hD, hclear⟩ := hM'
  refine ⟨D, hD, ?_⟩
  intro ℓ ℓ'
  let H := fun (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)) (s : ℂ) (a : A)
    (z : Langlands.GeneralLinear (n + 1) F.Carrier) =>
    equalRankFunction ψ (normalizedAbsoluteValue T) f.val f'.val Φ s
      (GeneralLinear.Iwasawa.diagonalUnits (d a) * z) * w a
  let B := fun f f' Φ s a => ∫ z, H f f' Φ s a z ∂κ
  let J := fun f f' Φ s => ∫ a, B f f' Φ s a ∂dA
  have hdata (f : (coefficientModel π ℓ).toSubmodule)
      (f' : (coefficientModel σ ℓ').toSubmodule)
      (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)) :
      (∃ b : ℝ, ∀ s : ℂ, b < s.re → Integrable (B f f' Φ s) dA ∧
        (∫⁻ a, ∫⁻ z, ‖H f f' Φ s a z‖ₑ ∂κ ∂dA) < ⊤) ∧
      ∃ R : RationalFunctions, HasRationalContinuation T.residueCardinality (J f f' Φ) R ∧
        R ∈ zetaSpan values := by
    obtain ⟨r, c, Ψ, _hc, _hmass, hformula⟩ := hexp ℓ ℓ' f f' Φ
    let S := fun (t : Fin r) (s : ℂ) (a : A) => ∑ j, I (η j) (Ψ t j) s a
    have hB (s : ℂ) (a : A) : B f f' Φ s a = ∑ t, (c t : ℂ) * S t s a :=
      (hformula a s).2.1
    have habs (s : ℂ) (a : A) :
        (∫⁻ z, ‖H f f' Φ s a z‖ₑ ∂κ) = ∑ t, ENNReal.ofReal (c t) * ‖S t s a‖ₑ :=
      (hformula a s).2.2
    choose b hb using fun (t : Fin r) (j : Fin m) => hconv (η j) (hmem j) (Ψ t j)
    obtain ⟨b₀, hb₀⟩ := (Set.finite_range (fun tj : Fin r × Fin m => b tj.1 tj.2)).bddAbove
    have hI (s : ℂ) (hs : b₀ < s.re) (t : Fin r) (j : Fin m) :
        Integrable (I (η j) (Ψ t j) s) dA :=
      hb t j s ((hb₀ (Set.mem_range_self (t, j))).trans_lt hs)
    have hS (s : ℂ) (hs : b₀ < s.re) (t : Fin r) : Integrable (S t s) dA :=
      integrable_finsetSum _ (fun j _ => hI s hs t j)
    have hJ (s : ℂ) (hs : b₀ < s.re) :
        J f f' Φ s = ∑ t, (c t : ℂ) * ∑ j, ∫ a, I (η j) (Ψ t j) s a ∂dA := by
      change (∫ a, B f f' Φ s a ∂dA) = _
      simp_rw [hB]
      rw [integral_finsetSum _ (fun t _ => (hS s hs t).const_mul (c t : ℂ))]
      apply Finset.sum_congr rfl
      intro t _
      rw [integral_const_mul]
      congr 1
      exact integral_finsetSum _ (fun j _ => hI s hs t j)
    refine ⟨⟨b₀, ?_⟩, ?_⟩
    · intro s hs
      constructor
      · simp_rw [show B f f' Φ s = fun a => ∑ t, (c t : ℂ) * S t s a from funext (hB s)]
        exact integrable_finsetSum _ (fun t _ => (hS s hs t).const_mul (c t : ℂ))
      · simp_rw [habs]
        rw [lintegral_finsetSum' Finset.univ
          (f := fun t a => ENNReal.ofReal (c t) * ‖S t s a‖ₑ)
          (fun t _ => aemeasurable_const.mul (hS s hs t).aestronglyMeasurable.enorm)]
        apply ENNReal.sum_lt_top.mpr
        intro t _
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (hasFiniteIntegral_iff_enorm.mp (hS s hs t).hasFiniteIntegral)
    · choose R hR using fun (t : Fin r) (j : Fin m) => hrat (η j) (hmem j) (Ψ t j)
      refine ⟨∑ t, RatFunc.C (c t : ℂ) * ∑ j, R t j, ?_, ?_⟩
      · apply continuation_of_eq_on_right
          (continuation_linear_combination Finset.univ (fun t => (c t : ℂ))
            (fun t s => ∑ j, ∫ a, I (η j) (Ψ t j) s a ∂dA)
            (fun t => ∑ j, R t j) (fun t _ =>
              continuation_sum Finset.univ _ (R t) (fun j _ => hR t j)))
        exact ⟨b₀, hJ⟩
      · apply Submodule.sum_mem
        intro t _
        have hsum : (∑ j, R t j) ∈ zetaSpan values := by
          apply Submodule.sum_mem
          intro j _
          exact mem_zetaSpan ⟨η j, hmem j, Ψ t j, hR t j⟩
        have hsmul := Submodule.smul_mem (zetaSpan values)
          (LaurentPolynomial.C (c t : ℂ)) hsum
        simpa only [Algebra.smul_def, algebraMap_laurent, laurentToRatFunc_C] using hsmul
  refine ⟨fun f f' Φ => (hdata f f' Φ).1, ?_, ?_⟩
  · intro f f' Φ
    obtain ⟨R, hR, _⟩ := (hdata f f' Φ).2
    exact ⟨R, hR⟩
  · intro f f' Φ R hR
    obtain ⟨S, hS, hspan⟩ := (hdata f f' Φ).2
    have heq : R = S := hR.unique T.residueCardinality_gt_one hS
    subst R
    exact denominator_clears_span D hclear hspan

end Langlands.RankinSelberg
