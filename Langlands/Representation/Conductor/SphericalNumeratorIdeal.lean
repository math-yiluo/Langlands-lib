import Langlands.Representation.Conductor.SphericalMinusculeCoefficient
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # The ideal of actual finite spherical numerators -/

noncomputable section

namespace Langlands.Conductor

open MvPolynomial
open scoped BigOperators

universe uK uσ uF uV uΛ

section Generators

variable (σ : Type uσ) (K : Type uK) [Fintype σ] [Field K]

theorem torusPolynomialAlgebraMap_injective :
    Function.Injective
      (algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K)) := by
  classical
  apply IsLocalization.injective (M := Submonoid.powers
    (∏ i : σ, (X i : MvPolynomial σ K))) (TorusPolynomialAlgebra σ K)
  exact powers_le_nonZeroDivisors_of_noZeroDivisors
    (Finset.prod_ne_zero_iff.mpr (fun i _ => X_ne_zero i))

/-- A symmetric Laurent polynomial has a symmetric polynomial numerator
after multiplication by a nonnegative power of the coordinate product. -/
theorem symmetricTorus_exists_polynomial_numerator
    (p : symmetricTorusSubalgebra σ K) :
    ∃ (m : ℕ) (a : symmetricSubalgebra σ K),
      p * (symmetricTorusDeterminantUnit σ K : symmetricTorusSubalgebra σ K) ^ m =
        symmetricPolynomialToTorus σ K a := by
  obtain ⟨m, a, ha⟩ :=
    IsLocalization.Away.surj (∏ i : σ, (X i : MvPolynomial σ K)) p.val
  have hs : a.IsSymmetric := by
    intro e
    apply torusPolynomialAlgebraMap_injective σ K
    have hprod : rename e (∏ i : σ, (X i : MvPolynomial σ K)) =
        ∏ i : σ, (X i : MvPolynomial σ K) := by
      simp only [map_prod, rename_X, Equiv.prod_comp]
    have he := congrArg (torusPolynomialPermutation σ K e) ha
    simp only [map_mul, map_pow, torusPolynomialPermutation_algebraMap,
      p.property e, hprod] at he
    exact he.symm.trans ha
  refine ⟨m, ⟨a, hs⟩, ?_⟩
  apply Subtype.ext
  change p.val * (torusDeterminantUnit σ K : TorusPolynomialAlgebra σ K) ^ m =
    algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) a
  simpa only [torusDeterminantUnit_val] using ha

/-- The elementary symmetric polynomials and inverse coordinate product
generate the full symmetric Laurent algebra. -/
theorem symmetricTorus_subalgebra_eq_top
    (S : Subalgebra K (symmetricTorusSubalgebra σ K))
    (he : ∀ k : ℕ, symmetricPolynomialToTorus σ K
      ⟨esymm σ K k, esymm_isSymmetric σ K k⟩ ∈ S)
    (hD : (((symmetricTorusDeterminantUnit σ K)⁻¹ :
      (symmetricTorusSubalgebra σ K)ˣ) : symmetricTorusSubalgebra σ K) ∈ S) :
    S = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨m, a, ha⟩ := symmetricTorus_exists_polynomial_numerator σ K p
  have hpoly : symmetricPolynomialToTorus σ K a ∈ S := by
    clear ha
    obtain ⟨b, rfl⟩ := esymmAlgHom_surjective K (le_refl (Fintype.card σ)) a
    induction b using MvPolynomial.induction_on with
    | C c =>
        simpa only [← MvPolynomial.algebraMap_eq, AlgHom.commutes] using
          S.algebraMap_mem c
    | add b c hb hc =>
        simpa only [map_add] using S.add_mem hb hc
    | mul_X b i hb =>
        rw [map_mul, map_mul]
        apply S.mul_mem hb
        simpa only [esymmAlgHom, aeval_X] using he (i.val + 1)
  have hm := S.pow_mem hD m
  have hp : p = (((symmetricTorusDeterminantUnit σ K)⁻¹ :
      (symmetricTorusSubalgebra σ K)ˣ) : symmetricTorusSubalgebra σ K) ^ m *
        symmetricPolynomialToTorus σ K a := by
    rw [← ha]
    simp only [mul_left_comm, ← mul_pow, Units.inv_mul, one_pow, mul_one]
  rw [hp]
  exact S.mul_mem hm hpoly

end Generators

section Multipliers

variable {K : Type uK} {A : Type uσ} [CommSemiring K] [CommSemiring A]
variable [Algebra K A]

/-- Multipliers preserving a given linear subspace form a subalgebra. -/
def submoduleMultiplierSubalgebra (U : Submodule K A) : Subalgebra K A where
  carrier := {b | ∀ a ∈ U, b * a ∈ U}
  zero_mem' a _ := by simpa only [zero_mul] using U.zero_mem
  add_mem' hb hc a ha := by
    simpa only [add_mul] using U.add_mem (hb a ha) (hc a ha)
  one_mem' a ha := by simpa only [one_mul] using ha
  mul_mem' {b c} hb hc a ha := by
    simpa only [mul_assoc] using hb (c * a) (hc a ha)
  algebraMap_mem' c a ha := by
    simpa only [Algebra.smul_def] using U.smul_mem c ha

end Multipliers

section Model

open MeasureTheory Langlands.GeneralLinear Langlands.Whittaker
open Langlands.GeneralLinear.Iwasawa Langlands.RankinSelberg
open Langlands.QuotientIntegration Langlands.HarmonicAnalysis

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}
variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
variable {ϖ : Fˣ} {μ : Measure (LeftUnipotentQuotient n F)}
variable (h : IsJacquetNormalization q ψ abv ϖ μ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (hπ : IsSmooth π) (ℓ : glFunctionals ψ (n + 1) π)
variable {Λ : Type uΛ} [Fintype Λ]
variable (hq : 0 < q) (hcard : Fintype.card Λ = q)
variable (hgeneric : ∀ i : Fin n, ∃ x : F,
  (ValuativeRel.valuation F) x * (ValuativeRel.valuation F) (ϖ : F) ≤ 1 ∧
    inverseStandardCharacter ψ n (Langlands.Whittaker.UpperUnipotentCharacter.adjacentUnit i x) ≠ 1)
variable (σ : Λ → F)
variable (hσ : ∀ x, σ x ∈ (ValuativeRel.valuation F).integer)
variable (hinj : ∀ x y, (ValuativeRel.valuation F) (σ x - σ y) < 1 → x = y)
variable (hsurj : ∀ z ∈ (ValuativeRel.valuation F).integer,
  ∃ x, (ValuativeRel.valuation F) (z - σ x) < 1)

include hq hcard hgeneric hσ hinj hsurj in
/-- Every symmetric Laurent multiplier preserves the actual numerator image. -/
theorem mul_mem_corankOneModelNumeratorSubmodule
    (P : Polynomial ℂ) (b a : symmetricTorusSubalgebra (Fin (n + 1)) ℂ)
    (ha : a ∈ corankOneModelNumeratorSubmodule h π hπ ℓ P) :
    b * a ∈ corankOneModelNumeratorSubmodule h π hπ ℓ P := by
  have htop : submoduleMultiplierSubalgebra
      (corankOneModelNumeratorSubmodule h π hπ ℓ P) = ⊤ := by
    apply symmetricTorus_subalgebra_eq_top
    · intro k a ha
      exact elementary_mul_mem_numeratorSubmodule h π hπ ℓ hq hcard
        hgeneric σ hσ hinj hsurj P k a ha
    · intro a ha
      simpa only [zpow_neg_one] using
        determinantUnit_zpow_mul_mem_numeratorSubmodule h π hπ ℓ P (-1) a ha
  have hb : b ∈ submoduleMultiplierSubalgebra
      (corankOneModelNumeratorSubmodule h π hπ ℓ P) := by
    rw [htop]
    trivial
  exact hb a ha

/-- The actual finite-support numerator image, with the proved ideal structure.
Its carrier is the existing linear image, rather than the ideal it generates. -/
def corankOneModelNumeratorIdeal (P : Polynomial ℂ) :
    Ideal (symmetricTorusSubalgebra (Fin (n + 1)) ℂ) where
  carrier := corankOneModelNumeratorSubmodule h π hπ ℓ P
  zero_mem' := (corankOneModelNumeratorSubmodule h π hπ ℓ P).zero_mem
  add_mem' := (corankOneModelNumeratorSubmodule h π hπ ℓ P).add_mem
  smul_mem' b a ha := mul_mem_corankOneModelNumeratorSubmodule h π hπ ℓ hq hcard
    hgeneric σ hσ hinj hsurj P b a ha

/-- Ideal membership still means an actual finite-support model-vector witness. -/
theorem mem_corankOneModelNumeratorIdeal_iff (P : Polynomial ℂ)
    (a : symmetricTorusSubalgebra (Fin (n + 1)) ℂ) :
    a ∈ corankOneModelNumeratorIdeal h π hπ ℓ hq hcard hgeneric σ hσ hinj hsurj P ↔
      ∃ (w : (coefficientModel π ℓ).toSubmodule)
        (hw : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite),
        corankOneModelNumerator h π hπ ℓ w P hw = a :=
  mem_corankOneModelNumeratorSubmodule_iff h π hπ ℓ P a

/-- The weak Nullstellensatz applies to the ideal of actual numerators. -/
theorem corankOneModelNumeratorIdeal_eq_top_of_no_common_zero (P : Polynomial ℂ)
    (hnonzero : ∀ x : Fin (n + 1) → ℂˣ,
      ∃ (w : (coefficientModel π ℓ).toSubmodule)
        (hw : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite),
        symmetricTorusEvaluation (Fin (n + 1)) ℂ x
          (corankOneModelNumerator h π hπ ℓ w P hw) ≠ 0) :
    corankOneModelNumeratorIdeal h π hπ ℓ hq hcard hgeneric σ hσ hinj hsurj P = ⊤ := by
  apply symmetricTorusIdeal_eq_top_of_no_common_zero
  intro x
  obtain ⟨w, hw, hx⟩ := hnonzero x
  exact ⟨corankOneModelNumerator h π hπ ℓ w P hw,
    (mem_corankOneModelNumeratorIdeal_iff h π hπ ℓ hq hcard
      hgeneric σ hσ hinj hsurj P _).mpr ⟨w, hw, rfl⟩, hx⟩

include hq hcard hgeneric hσ hinj hsurj in
/-- Pointwise nonvanishing yields a single actual model vector with numerator one. -/
theorem exists_corankOneModelNumerator_eq_one_of_no_common_zero (P : Polynomial ℂ)
    (hnonzero : ∀ x : Fin (n + 1) → ℂˣ,
      ∃ (w : (coefficientModel π ℓ).toSubmodule)
        (hw : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite),
        symmetricTorusEvaluation (Fin (n + 1)) ℂ x
          (corankOneModelNumerator h π hπ ℓ w P hw) ≠ 0) :
    ∃ (w : (coefficientModel π ℓ).toSubmodule)
      (hw : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite),
      corankOneModelNumerator h π hπ ℓ w P hw = 1 := by
  apply (mem_corankOneModelNumeratorIdeal_iff h π hπ ℓ hq hcard
    hgeneric σ hσ hinj hsurj P 1).mp
  rw [corankOneModelNumeratorIdeal_eq_top_of_no_common_zero h π hπ ℓ hq hcard
    hgeneric σ hσ hinj hsurj P hnonzero]
  trivial

end Model

end Langlands.Conductor
