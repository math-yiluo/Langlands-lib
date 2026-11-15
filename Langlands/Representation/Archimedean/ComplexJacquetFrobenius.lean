import Langlands.Representation.Archimedean.ComplexJacquetReduction
import Langlands.Representation.Archimedean.ComplexLanglandsQuotientReduction

/-!
# Frobenius reciprocity for Jacquet functionals of `(𝔤𝔩_n(ℂ), U(n))`-modules

A Jacquet functional `ℓ` of a `(𝔤𝔩_n(ℂ), U(n))`-module `(ρ, π)` on `V`, with exponents `a`,
`b` (`IsComplexJacquetFunctional`), gives a nonzero intertwining map from `V` into the
`U(n)`-finite functions of a principal series. For `g = β k` with `β` upper triangular and
`k ∈ U(n)`, it sends `v` to the function `g ↦ χ(β) ℓ(ρ(k) v)`, where `χ` is the character of
the upper triangular Borel subgroup cut out by `a` and `b`. This is Frobenius reciprocity
(Wallach 1979, 4.16–4.17), and it has two parts:

* `ComplexJacquetFrobeniusStatement`: the exponents determine `n` complex characters, with
  `a_j = 2 t_j + (n - 1) - 2 j` and `b_j = i l_j`, where `t_j` is the exponent and `l_j` the
  weight of the `j`-th character, and `V` maps nonzero into their standard module;
* `ComplexLanglandsSubrepresentationJacquetReductionStatement`: this, together with ordered
  Jacquet functionals (`ComplexOrderedJacquetFunctionalStatement`), implies the
  subrepresentation form of the Langlands classification,
  `ComplexLanglandsSubrepresentationStatement`. The theorem
  `complexLanglandsSubrepresentationJacquetReduction` proves the implication.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

universe uV

/-- Frobenius reciprocity for Jacquet functionals (Wallach 1979, 4.16–4.17, for `GL_n(ℂ)` and
its upper triangular Borel subgroup). Let `(ρ, π)` be a `(𝔤𝔩_n(ℂ), U(n))`-module and `ℓ` a
nonzero Jacquet functional with exponents `a`, `b`. Then there are `n` complex characters
`d 0, …, d (n-1)` with exponents `t_j` and weights `l_j` such that
`a_j = 2 t_j + (n - 1) - 2 j` and `b_j = i l_j`, and a nonzero intertwining map `B` from `V`
into the `U(n)`-finite functions of the standard module of these characters, in this order. -/
def ComplexJacquetFrobeniusStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsComplexGKModule n ρ π →
      ∀ (ℓ : V →ₗ[ℂ] ℂ) (a b : Fin n → ℂ), ℓ ≠ 0 → IsComplexJacquetFunctional n π ℓ a b →
        ∃ d : Fin n → ComplexCharacterData,
          (∀ j : Fin n, 2 * (d j).exponent + ((n : ℂ) - 1) - 2 * ((j : ℕ) : ℂ) = a j) ∧
          (∀ j : Fin n, Complex.I * ((d j).weight : ℂ) = b j) ∧
          ∃ B : V →ₗ[ℂ] kFiniteFunctions (complexStandardModule n (List.ofFn d))
              (unitaryCompact ℂ n),
            B ≠ 0 ∧ IsComplexStandardEmbedding n ρ π (List.ofFn d) B

/-- Frobenius reciprocity and ordered Jacquet functionals give the subrepresentation form of
the Langlands classification. -/
def ComplexLanglandsSubrepresentationJacquetReductionStatement : Prop :=
  ComplexJacquetFrobeniusStatement.{uV} → ComplexOrderedJacquetFunctionalStatement.{uV} →
    ComplexLanglandsSubrepresentationStatement.{uV}

/-- The real part of `a_j = 2 t_j + (n - 1) - 2 j`. -/
private theorem re_two_mul_add_sub (t : ℂ) (n j : ℕ) :
    (2 * t + ((n : ℂ) - 1) - 2 * ((j : ℕ) : ℂ)).re =
      2 * t.re + ((n : ℝ) - 1) - 2 * (j : ℝ) := by
  simp

/-- Proof of the reduction. Take an ordered Jacquet functional and its Frobenius map. The
ordering `Re a_i + 2 i ≤ Re a_j + 2 j` for `i < j` is `Re t_i ≤ Re t_j`, since
`Re a_j = 2 Re t_j + (n - 1) - 2 j`. -/
theorem complexLanglandsSubrepresentationJacquetReduction :
    ComplexLanglandsSubrepresentationJacquetReductionStatement.{uV} := by
  intro hFR hJ n V _ _ ρ π hgk hirr hadm
  obtain ⟨ℓ, a, b, hℓ, hJℓ, hord⟩ := hJ n V ρ π hgk hirr hadm
  obtain ⟨d, hda, -, B, hB, hBemb⟩ := hFR n V ρ π hgk ℓ a b hℓ hJℓ
  refine ⟨List.ofFn d, List.length_ofFn, ?_, B, hB, hBemb⟩
  rw [List.pairwise_ofFn]
  intro i j hij
  have h1 := hord i j hij
  rw [← hda i, ← hda j, re_two_mul_add_sub, re_two_mul_add_sub] at h1
  linarith

end Langlands.Archimedean
