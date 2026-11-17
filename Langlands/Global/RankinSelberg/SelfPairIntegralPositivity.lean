import Langlands.Global.RankinSelberg.SelfPairWhittaker
import Langlands.Global.RankinSelberg.SelfPairPositiveData
import Langlands.Global.RankinSelberg.DualExpansionFinal
import Langlands.Global.RankinSelberg.EqualUnfoldingKernel
import Langlands.Global.RankinSelberg.PartialIntegralExhaustion

/-! # Positivity of the global self-pair integral and a finite partial integral -/

noncomputable section
universe u
open NumberField MeasureTheory Filter
open scoped CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Global.RankinSelbergGlobal.SelfPair

open Automorphic

local instance integralPositiveSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance integralPositiveSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F]

/-- An integrable real function with positive total integral has a positive
integral over a partial Whittaker domain containing any prescribed finite set. -/
theorem exists_positive_partial_domain {n : ℕ}
    {f : WhittakerQuotient F n → ℝ} (hf : Integrable f (whittakerQuotientMeasure F n))
    (hpos : 0 < ∫ q, f q ∂whittakerQuotientMeasure F n)
    (S : Finset (FinitePlace F)) :
    ∃ A : Finset (FinitePlace F), S ⊆ A ∧
      0 < ∫ q in unipotentIntegralClasses F n A, f q ∂whittakerQuotientMeasure F n := by
  let : Countable (FinitePlace F) := finitePlace_countable F
  have hlim := tendsto_setIntegral_of_monotone
    (fun A : Finset (FinitePlace F) => measurableSet_unipotentIntegralClasses n A)
    (fun A B (hAB : A ⊆ B) => unipotentIntegralClasses_mono hAB) hf.integrableOn
  rw [iUnion_unipotentIntegralClasses n, Measure.restrict_univ] at hlim
  have hevent :
      ∀ᶠ A : Finset (FinitePlace F) in atTop,
        0 < ∫ q in unipotentIntegralClasses F n A, f q ∂whittakerQuotientMeasure F n :=
    hlim.eventually (isOpen_Ioi.mem_nhds hpos)
  obtain ⟨A, hA, hSA⟩ := (hevent.and (eventually_ge_atTop S)).exists
  exact ⟨A, hSA, hA⟩

variable [CompactSpace (AdeleQuotient F)]

/-- The quotient integrand of actual cusp Whittaker functions with a
Schwartz--Bruhat test function is continuous. -/
theorem continuous_equalWhittakerIntegrand {r : ℕ}
    (T T' : CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (x : T.Space) (x' : T'.Space) (Φ : RowVector F (r + 1) → ℂ)
    (hΦ : Φ ∈ schwartzBruhat F (r + 1)) (s : ℂ) :
    Continuous (equalWhittakerIntegrand F (cuspWhittaker F T ψ x)
      (cuspWhittaker F T' ψ⁻¹ x') Φ s) := by
  apply (LeftCosetSpace.continuous_iff (unipotentAdelic F (r + 1))).mpr
  change Continuous fun g : Points F (r + 1) =>
    equalWhittakerIntegrand F (cuspWhittaker F T ψ x)
      (cuspWhittaker F T' ψ⁻¹ x') Φ s
        (LeftCosetSpace.mk (unipotentAdelic F (r + 1)) g)
  simp_rw [EqualEulerIntegrand.equalWhittakerIntegrand_mk T T' ψ hψ x x' Φ s]
  exact (((Unfolding.continuous_cuspWhittaker' T ψ hψ x).mul
    (Unfolding.continuous_cuspWhittaker' T' ψ⁻¹
      (Unfolding.isStandardAdditiveCharacter_inv F ψ hψ) x')).mul
    ((EqualAnalytic.schwartzBruhat_properties F (r + 1) hΦ).1.comp
      (EqualUnfolding.continuous_lastRow F r))).mul
        (UnequalAnalytic.continuous_detPower F (r + 1) s)

/-- The global self-pair integral is positive at any real parameter where it is
integrable, provided its nonnegative test function is positive where the
Whittaker function is nonzero. -/
theorem equalWhittakerIntegral_conjugate_pos {r : ℕ}
    (T : CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (x : T.Space) (Φ : RowVector F (r + 1) → ℝ)
    (hΦ : (fun y => (Φ y : ℂ)) ∈ schwartzBruhat F (r + 1))
    (hΦnonneg : ∀ y, 0 ≤ Φ y) (g : Points F (r + 1))
    (hWg : cuspWhittaker F T ψ x g ≠ 0) (hΦg : 0 < Φ (lastRow F r g))
    (σ : ℝ)
    (hint : Integrable (equalWhittakerIntegrand F (cuspWhittaker F T ψ x)
      (cuspWhittaker F T.conjugate ψ⁻¹ (T.conjugateEquiv x))
      (fun y => (Φ y : ℂ)) σ) (whittakerQuotientMeasure F (r + 1))) :
    0 < (equalWhittakerIntegral F (cuspWhittaker F T ψ x)
      (cuspWhittaker F T.conjugate ψ⁻¹ (T.conjugateEquiv x))
      (fun y => (Φ y : ℂ)) σ).re := by
  let G := equalWhittakerIntegrand F (cuspWhittaker F T ψ x)
    (cuspWhittaker F T.conjugate ψ⁻¹ (T.conjugateEquiv x)) (fun y => (Φ y : ℂ)) (σ : ℂ)
  have hGc : Continuous G :=
    continuous_equalWhittakerIntegrand T T.conjugate ψ hψ x (T.conjugateEquiv x) _ hΦ σ
  have hGnonneg (q : WhittakerQuotient F (r + 1)) : 0 ≤ (G q).re := by
    rw [show G q = _ from
      equalWhittakerIntegrand_conjugate_real T ψ hψ.2.2.2 x Φ σ q]
    simp only [Complex.ofReal_re]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (hΦnonneg _)) (Real.exp_pos _).le
  have hGg :
      G (LeftCosetSpace.mk (unipotentAdelic F (r + 1)) g) =
        ((‖cuspWhittaker F T ψ x g‖ ^ 2 * Φ (lastRow F r g) *
          Real.exp (σ * Real.log (detNorm F (r + 1) g)) : ℝ) : ℂ) := by
    dsimp only [G]
    rw [EqualEulerIntegrand.equalWhittakerIntegrand_mk T T.conjugate
      ψ hψ x (T.conjugateEquiv x)]
    rw [cuspWhittaker_conjugate T ψ hψ.2.2.2]
    simp only [Complex.mul_conj', detPower, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_exp]
  have hne :
      (G (LeftCosetSpace.mk (unipotentAdelic F (r + 1)) g)).re ≠ 0 := by
    rw [hGg, Complex.ofReal_re]
    exact ne_of_gt (mul_pos (mul_pos (pow_pos (norm_pos_iff.mpr hWg) 2) hΦg)
      (Real.exp_pos _))
  let : (whittakerQuotientMeasure F (r + 1)).IsOpenPosMeasure :=
    isOpenPosMeasure_whittakerQuotientMeasure (r + 1)
  have hp := integral_pos_of_integrable_nonneg_nonzero
    (Complex.continuous_re.comp hGc) hint.re hGnonneg hne
  have hre : (∫ q, (G q).re ∂whittakerQuotientMeasure F (r + 1)) =
      (∫ q, G q ∂whittakerQuotientMeasure F (r + 1)).re := integral_re hint
  change 0 < ∫ q, (G q).re ∂whittakerQuotientMeasure F (r + 1) at hp
  rw [hre] at hp
  exact hp

/-- Positivity persists on some finite partial domain containing any prescribed
finite set. This conclusion only requires integrability at the selected real
parameter. -/
theorem exists_partialEqualWhittakerIntegral_conjugate_pos {r : ℕ}
    (T : CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (x : T.Space) (Φ : RowVector F (r + 1) → ℝ)
    (hΦ : (fun y => (Φ y : ℂ)) ∈ schwartzBruhat F (r + 1))
    (hΦnonneg : ∀ y, 0 ≤ Φ y) (g : Points F (r + 1))
    (hWg : cuspWhittaker F T ψ x g ≠ 0) (hΦg : 0 < Φ (lastRow F r g))
    (σ : ℝ)
    (hint : Integrable (equalWhittakerIntegrand F (cuspWhittaker F T ψ x)
      (cuspWhittaker F T.conjugate ψ⁻¹ (T.conjugateEquiv x))
      (fun y => (Φ y : ℂ)) σ) (whittakerQuotientMeasure F (r + 1)))
    (S : Finset (FinitePlace F)) :
    ∃ A : Finset (FinitePlace F), S ⊆ A ∧
      0 < (partialEqualWhittakerIntegral F A (cuspWhittaker F T ψ x)
        (cuspWhittaker F T.conjugate ψ⁻¹ (T.conjugateEquiv x))
        (fun y => (Φ y : ℂ)) σ).re := by
  have hp := equalWhittakerIntegral_conjugate_pos T ψ hψ x Φ hΦ hΦnonneg g hWg hΦg σ hint
  let G := equalWhittakerIntegrand F (cuspWhittaker F T ψ x)
    (cuspWhittaker F T.conjugate ψ⁻¹ (T.conjugateEquiv x)) (fun y => (Φ y : ℂ)) (σ : ℂ)
  have hre : (∫ q, (G q).re ∂whittakerQuotientMeasure F (r + 1)) =
      (∫ q, G q ∂whittakerQuotientMeasure F (r + 1)).re := integral_re hint
  have hp' : 0 < ∫ q, (G q).re ∂whittakerQuotientMeasure F (r + 1) := by
    rw [hre]
    exact hp
  obtain ⟨A, hSA, hA⟩ := exists_positive_partial_domain hint.re hp' S
  refine ⟨A, hSA, ?_⟩
  have hreA : (∫ q in unipotentIntegralClasses F (r + 1) A, (G q).re
      ∂whittakerQuotientMeasure F (r + 1)) =
      (∫ q in unipotentIntegralClasses F (r + 1) A, G q
        ∂whittakerQuotientMeasure F (r + 1)).re := integral_re hint.restrict
  change 0 < (∫ q in unipotentIntegralClasses F (r + 1) A, G q
    ∂whittakerQuotientMeasure F (r + 1)).re
  rw [← hreA]
  exact hA

/-- Internal positivity statement with integrability retained as a hypothesis. -/
def SelfPairIntegralPositivityStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ) (T : CuspidalOperatorRealization K r)
    (ψ : AddChar (Adeles K) ℂ), IsStandardAdditiveCharacter K ψ →
    ∀ (x : T.Space) (Φ : RowVector K (r + 1) → ℝ),
    (fun y => (Φ y : ℂ)) ∈ schwartzBruhat K (r + 1) →
    (∀ y, 0 ≤ Φ y) →
    ∀ g : Points K (r + 1), cuspWhittaker K T ψ x g ≠ 0 →
    0 < Φ (lastRow K r g) →
    ∀ σ : ℝ,
    Integrable (equalWhittakerIntegrand K (cuspWhittaker K T ψ x)
      (cuspWhittaker K T.conjugate ψ⁻¹ (T.conjugateEquiv x))
      (fun y => (Φ y : ℂ)) σ) (whittakerQuotientMeasure K (r + 1)) →
    ∀ S : Finset (FinitePlace K),
    ∃ A : Finset (FinitePlace K), S ⊆ A ∧
      0 < (equalWhittakerIntegral K (cuspWhittaker K T ψ x)
        (cuspWhittaker K T.conjugate ψ⁻¹ (T.conjugateEquiv x))
        (fun y => (Φ y : ℂ)) σ).re ∧
      0 < (partialEqualWhittakerIntegral K A (cuspWhittaker K T ψ x)
        (cuspWhittaker K T.conjugate ψ⁻¹ (T.conjugateEquiv x))
        (fun y => (Φ y : ℂ)) σ).re

/-- Proof by full support and exhaustion of the quotient. -/
theorem selfPairIntegralPositivity : SelfPairIntegralPositivityStatement.{u} := by
  intro K _ _ _ r T ψ hψ x Φ hΦ hΦnonneg g hWg hΦg σ hint S
  obtain ⟨A, hSA, hA⟩ :=
    exists_partialEqualWhittakerIntegral_conjugate_pos T ψ hψ x Φ hΦ hΦnonneg
      g hWg hΦg σ hint S
  exact ⟨A, hSA,
    equalWhittakerIntegral_conjugate_pos T ψ hψ x Φ hΦ hΦnonneg g hWg hΦg σ hint, hA⟩

end Langlands.Global.RankinSelbergGlobal.SelfPair
